import system.io 
@[reducible] meta def debruijn := nat

meta inductive folpred
| P : folpred
| T : folpred 
| eq : folpred

meta inductive folterm
| const : name → folterm -- Constant with given label
| lconst : name → name → folterm -- 
| prf : folterm
| var : debruijn → folterm -- Variable, but what is debruijn for? Are variables just specified by counter? X1,X2,X3,...
| app : folterm → folterm → folterm -- @(t,s) is the same as t s => apply t on input s

meta inductive folform 
| P : folterm → folform -- P(t) represents the provability of t
| T : folterm → folterm → folform -- T(t,τ) represents that t has type τ 
| eq : folterm → folterm → folform -- Equality. t == s
| bottom : folform -- Constant False
| top : folform -- Constant True
| neg : folform → folform -- Negation function. ¬A
| imp : folform → folform → folform -- Imply: A → B
| iff : folform → folform → folform -- Two-sided imply/iff: A ↔ B
| conj : folform → folform → folform -- Conjunction: A ∧ B
| disj : folform → folform → folform -- Disjunction: A ∨ B
| all : name → name → folform → folform -- For all: ∀ (a : α) t -- a and α are the names, t the formula 
| exist : name → name → folform → folform -- Exists: ∃ (a : α) t -- Similar as above

meta structure introduced_constant := -- Structure representing a new constant introduced for translation
(n : name) (e : expr) -- name and type

meta structure axioma := -- Note: axiom is reserved word in Lean, thus the additional a
(n : name) (f : folform) -- Every axiom is specified by a name and its formula

meta structure hammer_state := -- Structure representing the state of the hammer (list of axioms with corresponding list of newly introduced constants for translation)
(axiomas : list axioma)
(introduced_constants : list introduced_constant)

meta def hammer_tactic :=
state_t hammer_state tactic

section tptp
open format
-- Used functions from this set
--   1) to_fmt: {α : Type} (a : α) := a → format => returns a format object for an instance of any type
--   2) 

-- axiom is a reserved word in Lean
meta inductive role -- Role of a formula. Can be either axiom or conjecture (for tptp format)
| axioma : role
| conjecture : role

meta def role.to_format : role → format -- Probably decide how to print a formula?
| role.axioma := to_fmt "axiom"
| role.conjecture := to_fmt "conjecture"

meta instance : has_to_format role := -- What is this for?
⟨role.to_format⟩

 -- Retrieve a list of all free variables for a given formula, and return it as cartesian product (why as cartesian product?)
 -- Only looks at the name but not the type of the variable...
meta def folform.to_format_collect_vars : folform → list name → (list name × folform)
| (folform.all n n1 e@(folform.all _ _ _)) xs := folform.to_format_collect_vars e (n :: xs)
| (folform.exist n n1 e@(folform.exist _ _ _)) xs := folform.to_format_collect_vars e (n :: xs)
| (folform.all n n1 e) xs := ((n :: xs).reverse, e)
| (folform.exist n n1 e) xs := ((n :: xs).reverse, e)
| e@_ xs := (xs.reverse, e)

-- Print name
meta def name_to_id_format : name → format
| n := "'" ++ to_fmt n ++ "'"

-- For a list of (probably free) variables, print out the name by calling V1, V2, ... with element x
meta def names_to_id_format : list name → nat → list format
| (x::xs) d := ("V" ++ to_fmt (d+1) ++ " /* " ++ to_fmt x ++ " */") :: names_to_id_format xs (d+1)
| [] d := []

-- For what do I have to define this type? It is an identity mapping of input to output
meta def mygroup : format → format := id -- @[inline] def id {α : Sort u} (a : α) : α := a

-- Convert term into format. Second argument defines the depth (number of free variables that already have been defined in this formula)
meta def folterm.to_format : folterm → nat → format
| (folterm.const n) _ := "'" ++ to_fmt n ++ "'" -- A constant is converted into its name itself
| (folterm.lconst n _) _ := "'" ++ to_fmt n ++ "'" -- A long(?) constant is processed the same way
| (folterm.prf) _ := "prf" -- A proof is printed out as proof (is this a tptp convention?)
| (folterm.var i) depth := "V" ++ to_fmt (depth - i) -- Variable indicated by "V" and number. Last defined variable has number i=0, then it goes up to depth-1
| (folterm.app t u) depth := -- Apply t on u -> a('t', 'u')
  "a(" ++ t.to_format depth ++ "," ++
    (mygroup $ nest 2 $ line ++ u.to_format depth) ++ ")" -- Lean notation: "a $ b c" is the same as "a (b c)", just simplifies notation of brackets

-- Convert formula into format with extra input 
-- depth: defines number of free variables that already have been defined
meta def folform.to_format_aux : folform → nat → format
-- For-all operator ∀ n:n1, f
| e@(folform.all n n1 f) depth := 
  let (ys, g) := folform.to_format_collect_vars e [] in -- Define (ys,g) as the expression for all following statements
  let ys' := names_to_id_format ys depth in
    "! [" ++ -- ! is TPTP expression for ∀ 
    (mygroup $ nest 3 $ (join $ list.intersperse ("," ++ line) ys') ++ "] :") ++ -- Print list of free variables
    -- list.intersperse: put new element ","+newline between all elements. Similar to " ".join(list) in python
    -- join: Composes multiple formats into one by (similar to) concatenating the single formats/strings
    (mygroup $ nest 2 $ line ++ "(" ++ (mygroup $ nest 1 $ g.to_format_aux $ depth + ys.length)) ++ ")" -- Print subformula with different depth!
-- There-exists operator ∃ n:n1, f
| e@(folform.exist n n1 f) depth :=
  -- Same process as ∀ but only change "!" by "?" for TPTP output
  let (ys, g) := folform.to_format_collect_vars e [] in
  let ys' := names_to_id_format ys depth in
    "? [" ++ 
    (mygroup $ nest 3 $ (join $ list.intersperse ("," ++ line) ys') ++ "] :") ++
    (mygroup $ nest 2 $ line ++ "(" ++ (mygroup $ nest 1 $ g.to_format_aux $ depth + ys.length)) ++ ")"
-- Constant false
| folform.bottom _ := to_fmt "$false"
-- Constant true
| folform.top _ := to_fmt "$true"
-- Stating p function (p(t) returns whether t is proofable or not)
| (folform.P t) depth :=
  "p(" ++ (nest 2 $ t.to_format depth) ++ ")"
-- Stating t function (T(t,u) returns whether t is of type u)
| (folform.T t u) depth :=
  "t(" ++ (mygroup $ nest 2 $ t.to_format depth ++ "," ++ line ++ u.to_format depth ++ ")")
-- Equality relation t=u
| (folform.eq t u) depth :=
  "(" ++ (nest 1 $ t.to_format depth ++
    (mygroup $ line ++ "= " ++ (nest 2 $ u.to_format depth ++ ")")))
-- Negate f. If f is equality relation, just negate this one
| (folform.neg f) depth := 
  match f with
  | (folform.eq t u) := -- Equality relations are negated by '!=' instead of '~(...=...)'
    "(" ++ (nest 1 $ t.to_format depth ++
      (mygroup $ line ++ "!= " ++ (nest 3 $ u.to_format depth ++ ")")))
  | _ := "~(" ++ (nest 2 $ f.to_format_aux depth ++ ")")
  end
-- Imply f → g with token '=>' in TPTP notation
| (folform.imp f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++ 
    (mygroup $ line ++ (nest 4 $ "=> (" ++ g.to_format_aux depth ++ ")"))
-- Iff similar to imply
| (folform.iff f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++
    (mygroup $ line ++ (nest 5 $ "<=> (" ++ g.to_format_aux depth ++ ")"))
-- Conjecture f ∧ g
| (folform.conj f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++
    (mygroup $ line ++ (nest 3 $ "& (" ++ g.to_format_aux depth ++ ")"))
-- Disjunction f ∨ g
| (folform.disj f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++
    (mygroup $ line ++ (nest 3 $ "| (" ++ g.to_format_aux depth ++ ")"))
     
-- For outer formulas, start with depth 0 (all others use recursive function above)
meta def folform.to_format (f : folform) : format := folform.to_format_aux f 0

-- What for is this instance?
meta instance : has_to_format folform :=
⟨folform.to_format⟩

-- Convert formula with name and role to output string
meta def to_fof : string → role → folform → format
| id r f :=
to_fmt "fof("
++ (mygroup $ nest 4 $ join $ list.intersperse ("," ++ line) $ -- Combine all parts by "," and new line
  [to_fmt id, to_fmt r, "(" ++ (mygroup $ nest 1 $ to_fmt f) ++ ")"]) ++ to_fmt ")." -- Output: fof(name, role, (formula)).
  
-- Combine list of axioma into single string
meta def to_tptp : list axioma → folform → format
| (⟨n, f⟩::as) conjecture := 
  to_fof ("'" ++ to_string n ++ "'") role.axioma f
     ++ line
     ++ line
     ++ to_tptp as conjecture
| [] conjecture := to_fof "'problem_conjecture'" role.conjecture conjecture

-- What do we need this constant for?
-- For a list of elements, call "to_fmt" function and return as single string '[...]'
meta def myformat {α : Type} [has_to_format α] : list α → format
| [] := to_fmt "[]"
| xs := to_fmt "[" ++ mygroup (format.nest 1 $ format.join $ list.intersperse ("," ++ format.line) $ xs.map to_fmt) ++ to_fmt "]"

end tptp 



-----------------------------------
----      Debug functions      ----
-----------------------------------
--  1) Print out a formula as it is
--  2) Print a formula in TPTP form

meta def name.repr : name → string
| name.anonymous := "name.anonymous"
| (name.mk_numeral n p) := "(name.mk_numeral " ++ repr n ++ " " ++ name.repr p ++ ")"
| (name.mk_string s p) := "(name.mk_string " ++ repr s ++ " " ++ name.repr p ++ ")"

meta instance : has_repr name :=
⟨name.repr⟩

meta def folterm.repr : folterm → string 
| (folterm.const n) := "(folterm.const " ++ repr n ++ ")"
| (folterm.lconst n n1) := "(folterm.lconst " ++ repr n ++ " " ++ repr n1 ++ ")"
| folterm.prf := "folterm.prf"
| (folterm.var n) := "(folterm.var " ++ repr n ++ ")"
| (folterm.app t1 t2) := "(folterm.app " ++ folterm.repr t1 ++ " " ++ folterm.repr t2 ++ ")"

meta instance : has_repr folterm :=
⟨folterm.repr⟩

meta def folpred.repr : folpred → string
| folpred.P := "folpred.P"
| folpred.T := "folpred.T"
| folpred.eq := "folpred.eq"

meta instance : has_repr folpred :=
⟨folpred.repr⟩

meta def folform.repr : folform → string
| (folform.P t) := "(folform.P " ++ repr t ++ ")"
| (folform.T t u) := "(folform.T " ++ repr t ++  " " ++ repr u ++ ")"
| (folform.eq t u) := "(folform.eq " ++ repr t ++  " " ++ repr u ++ ")"
| folform.bottom := "folform.bottom"
| folform.top := "folform.top"
| (folform.neg f) := "(folform.neg " ++ folform.repr f ++ ")"
| (folform.imp f g) := "(folform.imp " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.iff f g) := "(folform.iff " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.conj f g) := "(folform.conj " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.disj f g) := "(folform.disj " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.all n n1 f) := "(folform.all " ++ repr n ++ " " ++ repr n1 ++ " " ++ folform.repr f ++ ")"
| (folform.exist n n1 f) := "(folform.exist " ++ repr n ++ " " ++ repr n1 ++ " " ++ folform.repr f ++ ")"

meta instance : has_repr folform :=
⟨folform.repr⟩

meta def example_formula : folform :=
folform.all `h1 `h1 $ folform.all `h2 `h2 $ -- folform.all `h3 `h3 $ 
  folform.neg $
  folform.iff
    (folform.conj
      (folform.neg $ folform.eq (folterm.var 0) (folterm.var 1)) 
      (folform.eq (folterm.var 0) (folterm.var 1)) )
    (folform.imp
      (folform.conj (folform.P $ folterm.var 0) (folform.disj (folform.P $ folterm.var 0) (folform.P $ folterm.var 1)))
      (folform.T (folterm.var 0) (folterm.app (folterm.var 1) (folterm.var 0))))

meta def example_formula2 : folform :=
folform.imp (folform.conj (folform.P $ folterm.const "n") (folform.P $ folterm.const "a"))
(folform.T (folterm.const "n") (folterm.app (folterm.const "n") (folterm.const("a"))))


-- #eval tactic.trace $ to_fof "example_formula" role.axioma example_formula  
-- #eval tactic.trace $ to_fof "example_formula2" role.conjecture example_formula2  
-- #eval tactic.trace example_formula.repr 

-- meta def axiomas_to_fof : list axioma → string
-- | nil := ""
-- | (x :: xs) := (to_fof _ role.axioma x) ++ axiomas_to_fof xs



-----------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------



meta instance : monad hammer_tactic :=
state_t.monad 

meta instance (α : Type) : has_coe (tactic α) (hammer_tactic α) :=
⟨state_t.lift⟩


meta def using_hammer {α} (t : hammer_tactic α) : tactic (α × hammer_state) :=
do let ss := hammer_state.mk [] [],
   state_t.run t ss -- (do a ← t, return a) 

meta def when' (c : Prop) [decidable c] (tac : hammer_tactic unit) : hammer_tactic unit :=
if c then tac else tactic.skip

meta def lives_in_prop_p (e : expr) : hammer_tactic bool :=
do tp ← tactic.infer_type e,
   return (if eq tp (expr.sort level.zero) then tt else ff)

meta def lives_in_type (e : expr) : hammer_tactic bool :=
do tp ← tactic.infer_type e,
   return (if eq tp (expr.sort (level.succ (level.succ level.zero))) then tt else ff)

meta def add_axiom (n : name) (axioma : folform) : hammer_tactic unit :=
do state_t.modify (fun state, {state with axiomas := ⟨n, axioma⟩ :: state.axiomas})

meta def add_constant (n : name) (e : expr) : hammer_tactic unit :=
do state_t.modify (fun state, {state with introduced_constants := ⟨n, e⟩ :: state.introduced_constants })


-- might want to do something different
meta def mk_fresh_name : tactic name := tactic.mk_fresh_name

-- 
meta def body_of : expr → hammer_tactic (expr × name)
| e@(expr.pi n bi d b) := do id ← mk_fresh_name,
                             let x := expr.local_const id n bi d,
                             return $ prod.mk (expr.instantiate_var b x) id
| e@(expr.lam n bi d b) := do id ← mk_fresh_name,
                             let x := expr.local_const id n bi d,
                             return $ prod.mk (expr.instantiate_var b x) id                           
| e := return (e, name.anonymous)
                    
meta def folterm.abstract_locals_core : folterm → ℕ → list name → folterm
| e@(folterm.lconst n n1) d ln :=
  list.foldl
    (λ e' n', if n = n' then folterm.var $ d + ln.reverse.find_index (= n) else e')
    e
    ln
| (folterm.app t1 t2) d ln := folterm.app (t1.abstract_locals_core d ln) (t2.abstract_locals_core d ln)
| e d ln := e

meta def folterm.abstract_locals : folterm → list name → folterm := λ f l, f.abstract_locals_core 0 l

meta def folform.abstract_locals_core : folform → nat → list name → folform
| e@(folform.P t) d ln := folform.P $ t.abstract_locals_core d ln
| e@(folform.T t u) d ln := folform.T (t.abstract_locals_core d ln) (u.abstract_locals_core d ln)
| e@(folform.eq t u) d ln := folform.eq (t.abstract_locals_core d ln) (u.abstract_locals_core d ln)
| e@(folform.neg f) d ln := folform.neg (f.abstract_locals_core d ln)
| e@(folform.imp f1 f2) d ln := folform.imp (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.iff f1 f2) d ln := folform.iff (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.conj f1 f2) d ln := folform.conj (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.disj f1 f2) d ln := folform.disj (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.all n n1 f) d ln := folform.all n n1 (f.abstract_locals_core (d+1) ln)
| e@(folform.exist n n1 f) d ln := folform.exist n n1 (f.abstract_locals_core (d+1) ln)
| e d ln := e

meta def folform.abstract_locals : folform → list name → folform := λ f l, f.abstract_locals_core 0 l

-- FC(Γ;Πx:t.s): List of free variables in expression excluding x in s
meta def hammer_fc (e: expr) : list $ name × name × expr :=
expr.fold e []
  (λ (e : expr) n l, 
    match e with
    | e@(expr.local_const n n1 _ t) := let e := (n, n1, t) in if e ∉ l then e::l else l
    | _ := l
    end)

-- Set of free variables that are not Γ proofs
meta def hammer_ff (l : list $ name × name × expr) : hammer_tactic $ list $ name × name :=
do  exprs ← list.mfilter
      (λ x, let (⟨_, _, t⟩ : name × name × expr) := x in
        do  lip ← lives_in_prop_p t,
            return ¬lip)
      l, 
    return $ list.foldl
      (λ a (x : name × name × expr), let (⟨n, n1, t⟩ : name × name × expr) := x in
        ⟨n, n1⟩ :: a)
      [] exprs 

meta def wrap_quantifier (binder : name → name → folform → folform) (ns : list $ name × name) (f : folform) : folform :=
list.foldr
  (λ (np : name × name) f, binder np.1 np.2 f)
  (folform.abstract_locals f (list.map (λ (np : name × name), np.1) ns))
  ns      

meta def collect_lambdas_aux :
    (expr × (list $ name × name × expr)) → 
    hammer_tactic (expr × (list $ name × name × expr))
| (e@(expr.lam n _ t _), l) := do (b, xn) ← body_of e, collect_lambdas_aux (b, (xn, n, t) :: l)
| a := return a

meta def remove_suffix_of_string : list char → list char 
| ['.','_','m','a','i','n'] := []
-- | ('.' :: '_' :: b) := [] -- What about other suffixes than main?
| (a :: b) := ([a] ++ remove_suffix_of_string b)
| [] := []

meta def collect_lambdas (e : expr) := collect_lambdas_aux (e, [])

-- == Translating terms ==
-- Function F encodes propositions as FOL formulas
-- Function G encodes types as guards
-- Function C encodes CIC0 terms as FOL terms
meta mutual def hammer_c, hammer_g, hammer_f
-- Define function C (encodes CIC_0 terms as FOL terms)
with hammer_c : expr → hammer_tactic folterm 
| e@(expr.const n _) := 
  do 
    -- TODO deviation from specification, map constants : sth : Prop to prf
    -- is this necessary?
    -- tactic.trace e,
    t ← tactic.infer_type e, -- consult the environment (get type of expression)
    lip ← lives_in_prop_p t, -- check whether t is prop or not
    if lip
    then
      return $ folterm.prf -- What about the type/formula it actually proofs?
    else
      return $ folterm.const $ (remove_suffix_of_string n.to_string.to_list).as_string 
| (expr.local_const n pp _ t) := -- Same for local constants
  do  lip ← lives_in_prop_p t,
      if lip
      then
        return $ folterm.prf
      else
        return $ folterm.lconst n pp
| (expr.app t s) := -- Application (in paper C_Γ(ts)=...)
  do  tp ← hammer_c t, -- Get C_Γ(t)
      sp ← hammer_c s, -- Get C_Γ(s)
      match tp with
      | folterm.prf := return folterm.prf -- If C_Γ(t) is type proof, then just return type proof
      | _ := -- Anything else: check what type C_Γ(s) has
        match sp with
        | folterm.prf := return tp -- If it is a proof, return C_Γ(t)
        | _ := return $ folterm.app tp sp -- else: Return C_Γ(t) applied on C_Γ(s)
        end
      end
| e@(expr.pi n _ t _) := -- Dependent types (in paper C_Γ(Πx:t.s) )
  do  lip ← lives_in_prop_p e,
      Fn ← mk_fresh_name,
      let F := folterm.const Fn, -- Fresh constant F
      let An := n ++ Fn, -- Axiom name
      ys ← hammer_ff $ hammer_fc e, -- y = FF_Γ(FC(Γ;Πx:t.s))
      let ce0 := list.foldl (λ t (np : name × name), folterm.app t (folterm.lconst np.1 np.2)) F ys, -- Fy (for all elements in ys, apply F on them by creating local constant of the name)
      if lip 
      then -- If s is of type Prop: new axiom ∀y.P(Fy) ↔ F_Γ(Πx:t.s)  
        (do let ce1 := folform.P ce0, 
            ce2 ← hammer_f e, -- F_Γ(Πx:t.s)   
            add_axiom An $ wrap_quantifier folform.all ys (folform.iff ce1 ce2)) -- Add new axiom to tactic
      else -- Otherwise: new axiom ∀yz.T(z,Fy) ↔ G_Γ(z,Πx:t.s)  
        (do zn ← mk_fresh_name, -- Get new, fresh constant name
            let zlc := folterm.lconst zn zn, -- Create local constant from this name
            let ys := (⟨zn, zn⟩ :: ys : list $ name × name), -- Add this constant to the already existing set of free variables of our formula
            let ce1 := folform.T zlc ce0, -- type checker T(z,Fy)
            ce2 ← hammer_g zlc e, -- type guard G_Γ(z,Πx:t.s) 
            add_axiom An $ wrap_quantifier folform.all ys (folform.iff ce1 ce2)), -- Add new axiom to tactic
      return ce0 -- Return Fy (what for is this necessary?)
| e@(expr.lam n _ _ _) := -- Lambda expression C_Γ(λx:τ.t)=Fy_0
  do  (t, xτs) ← collect_lambdas e, -- Get all lambda expressions in e
      -- tactic.trace e,
      α ← tactic.infer_type t, -- Infer the type of t given all lambda expression (Γ,x:τ|-t:α)
      let yρs := hammer_fc e, -- y: ρ = FC(Γ;λx:τ.t) - Get list of free constants in e
      Fn ← mk_fresh_name, -- Fresh constant name
      let An := n ++ Fn, -- ??? Add new constant name to list of current constants(?)
      y₀s ← hammer_ff yρs, -- 
      x₀s ← hammer_ff xτs, -- 
      let Ft :=
        list.foldr
          (λ (nt : name × name × expr) a,
            expr.pi nt.2.1 binder_info.default nt.2.2 $ expr.abstract_local a nt.1)
          α
          $ yρs ++ xτs,
      -- instead of extending the environment, we use a local constant and keep track of its name
      add_constant Fn Ft,
      let F := @expr.local_const tt Fn Fn binder_info.default Ft,
      let (ce1a : expr) :=
        list.foldl 
          (λ (a : expr) (nt : name × name × expr), (a (expr.local_const nt.1 nt.2.1 binder_info.default nt.2.2)))
          F
          $ yρs ++ xτs,  
      -- TODO two approaches:
      my_eq ← tactic.mk_const `eq,
      my_iff ← tactic.mk_const `iff,
      lip ← lives_in_prop_p ce1a,
      let ce1b' := if lip then (my_iff ce1a t) else (my_eq α ce1a t),
      -- ce1b ← tactic.to_expr ``(eq %%ce1a %%t), 
      -- tactic.to_expr is going to blow up if operands are not of the same type. Exciting.
      ce1 ← hammer_f ce1b',
      add_axiom An $ wrap_quantifier folform.all (y₀s ++ x₀s) ce1,
      return $
        list.foldl
          (λ a (nt : name × name), folterm.app a $ folterm.lconst nt.1 nt.2)
          (folterm.const Fn)
          y₀s
| e@(expr.elet x τ t s) :=
  do  let yαs := hammer_fc (t τ),  
      y₀s ← hammer_ff yαs,
      Fn ← mk_fresh_name,
      let An := x ++ Fn,
      let Ft :=
        list.foldr
          (λ (nt : name × name × expr) a,
            expr.pi nt.2.1 binder_info.default nt.2.2 $ expr.abstract_local a nt.1)
          τ
          $ yαs,
      -- deviation from the specification, since I cannot imagine why a definition
      -- instead of a constant is required since the redexes F... are not going to be
      -- reduced
      -- instead of extending the environment, we use a local constant and keep track of its name
      add_constant Fn Ft,
      tactic.add_decl $ declaration.cnst Fn [] Ft tt,
      let F := expr.local_const Fn Fn binder_info.default Ft,
      let ce1 :=
        list.foldl
          (λ (e : expr) (nt : name × name × expr), (e (expr.local_const nt.1 nt.2.1 binder_info.default nt.2.2))) 
          F
          yαs,
      -- TODO deviation from the specification, we use yαs here instead of y₀s.
      -- I presume the specification is some sort of "optimization" since since
      -- Gamma-proof terms are going to be filtered by the definition of hammer_c
      -- anyway, however infer_type is not going to blow up but it will report
      -- incorrect types if the arguments to a function are in the wrong positions
      lip ← lives_in_prop_p Ft,
      if lip
      then
        do  ce2 ← hammer_c t,
            add_axiom An $ wrap_quantifier folform.all y₀s $
              folform.eq 
                (list.foldl (λ e (nt : name × name), (folterm.app e (folterm.const nt.1))) (folterm.const Fn) y₀s)
                ce2
      else
        return (),
      hammer_c $ expr.instantiate_var s ce1
-- TODO: Check if those need to be implemented as well
| e@(expr.var _) := -- do tactic.trace e, 
                    undefined
-- NEED TO BE IMPLEMENTED
| e@(expr.sort _) := do tactic.trace e, 
                     undefined
                     -- hammer_c `(5)
| e@(expr.mvar _ _ _) := -- do tactic.trace e, 
                         undefined
| e@(expr.macro _ _) := -- do tactic.trace e, 
                        undefined

-- Define function G (encodes types as guards)
with hammer_g : folterm → expr → hammer_tactic folform
| u w@(expr.pi n _ t _) := 
  do  lip ← lives_in_prop_p t,
      if lip
      then 
        do  ge1 ← hammer_f t,
            (s, _) ← body_of w,
            ge2 ← hammer_g u s,
            -- tactic.trace ge1,
            -- tactic.trace ge2,
            -- tactic.trace $ folform.imp ge1 ge2,
            return $ folform.imp ge1 ge2
      else
        do  (s, xn) ← body_of w,
            ge1 ← hammer_g (folterm.lconst xn n) t,
            ge2 ← hammer_g (folterm.app u (folterm.lconst xn n)) s,
            -- tactic.trace ge1,
            -- tactic.trace ge2,
            return $ wrap_quantifier folform.all [(xn, n)] (folform.imp ge1 ge2)
| u w :=
  do  ge1 ← hammer_c w,
      return $ folform.T u ge1

-- Define function F (encodes propositions as FOL formulas)
with hammer_f : expr → hammer_tactic folform 
| e@(expr.pi n _ t _) :=
  do  lip ← lives_in_prop_p t,
      if lip 
      then
        do  fe1 ← (hammer_f t),
            (s, _) ← body_of e,
            fe2 ← hammer_f s,
            return $ folform.imp fe1 fe2
      else
        do  (s, xn) ← body_of e,
            fe1 ← hammer_g (folterm.lconst xn n) t,
            fe2 ← hammer_f s,
            return $ wrap_quantifier folform.all [(xn, n)] (folform.imp fe1 fe2)
-- For all is eventually missing. How to implement? It must be forwarded to second case of expr.pi
--| e@`(@Forall %%t %%ps) := 
| e@`(@Exists %%t %%ps) := -- we cannot assume that ps has the shape of a lambda
  do  xn ← mk_fresh_name,
      let lc := expr.local_const xn xn binder_info.default t,
      s ← tactic.whnf (ps lc),
      fe1 ← hammer_g (folterm.lconst xn xn) t,
      fe2 ← hammer_f s,
      return $ wrap_quantifier folform.exist [(xn, xn)] (folform.conj fe1 fe2) 
| e@`(and %%t %%s) :=
  do  fe1 ← hammer_f t,
      fe2 ← hammer_f s,
      return $ folform.conj fe1 fe2
| `(or %%t %%s) :=
  do  fe1 ← hammer_f t,
      fe2 ← hammer_f s,
      return $ folform.disj fe1 fe2
| `(iff %%t %%s) :=
  do  fe1 ← hammer_f t,
      fe2 ← hammer_f s,
      return $ folform.iff fe1 fe2                       
| `(not %%t) :=
  do  fe1 ← hammer_f t,
      return $ folform.neg $ fe1  
| `(%%t = %%s) :=
  do  fe1 ← hammer_c t,
      fe2 ← hammer_c s,
      return $ folform.eq fe1 fe2                                                    
| t  :=
  do  ge1 ← hammer_c t,
      return $ folform.P ge1

-- == Notes from former student ==
-- TODO negation, false? Map to bottom etc.
-- eprover, vampire

--###################
--## Testing stuff ##
--###################

open expr 



-- run_cmd do (ge12, _) <- (using_hammer (hammer_f (`(fib 0)))), tactic.trace $ to_fof "example_formula1" role.axioma ge12
-- run_cmd do (ge12, _) <- (using_hammer (hammer_f (`((nat.succ 1) = 1+1)))), tactic.trace $ to_fof "example_formula1" role.axioma ge12
-- run_cmd do (ge12, _) <- (using_hammer (hammer_f (`((nat.succ 1) = 2)))), tactic.trace $ to_fof "example_formula2" role.axioma ge12
-- run_cmd do (ge12, _) <- (using_hammer (hammer_f (`(1+1 = 2)))), tactic.trace $ to_fof "example_formula3" role.conjecture ge12

--##################################
--## 5.3 Translating declarations ##
--##################################

meta def translate_axiom_expression: expr → hammer_tactic unit
-- | `()
| `(%%l = %%r) := -- c = t : τ
  do  (τ, _) ←  using_hammer $ tactic.infer_type r, -- Get type of right side
      -- tactic.trace l,
      -- tactic.trace r,
      lip <- lives_in_prop_p τ, -- Check whether τ is from type prop (and therefore right side a proof) or not
      if lip 
      then -- If yes, add new axiom of F(τ) (TODO: and name c) 
        do  fe1 ← (hammer_f τ),
             Cn ← mk_fresh_name,
             add_axiom Cn fe1
      else -- Otherwise, add type checker G(c,τ) as new axiom
        do  (c,_) <- using_hammer (hammer_c l),
             g_axiom <- hammer_g c τ,
             Cn ← mk_fresh_name,
             add_axiom Cn g_axiom,
             lit <- lives_in_prop_p r, -- Check if τ=Prop (or rather t : Prop)
             if lit
             then -- If yes, add new axiom c ↔ F(t)
              do  (fe1,_) <- using_hammer (hammer_f l),
                  (fe2,_) <- using_hammer (hammer_f r),
                  Cn ← mk_fresh_name,
                  add_axiom Cn (folform.iff fe1 fe2)
            else -- Otherwise, check whether τ is from type Set or Type, or another type
              do  lis <- lives_in_type r, -- WRONG IMPLEMENTATION! TODO: Implement check of τ for Set and Type!
                if lis
                then 
                  do  xn ← mk_fresh_name,
                      let f := folterm.lconst xn xn,
                      -- a <- wrap_quantifier folform.all [(xn, xn)] (folform.iff (hammer_c $ folterm.app c f) (hammer_g f r)),
                      -- TODO: Implement the correct formula
                      let a := folform.top,
                      Cn <- mk_fresh_name,
                      add_axiom Cn a 
                else
                  do  Cn <- mk_fresh_name,
                      (Cc,_) <- using_hammer (hammer_c r),
                      (Ct,_) <- using_hammer (hammer_c l),
                      add_axiom Cn (folform.eq Cc Ct)
-- Inductive declarations are handled in advance. Thus we don't have to check for them anymore
| `(%%c : _) := -- c : τ 
  do (τ, _) ←  using_hammer $ tactic.infer_type c, -- Get type of right side
      -- tactic.trace c,
      lip <- lives_in_prop_p τ, -- Check whether τ is from type prop (and therefore right side a proof) or not
      -- tactic.trace τ,
      -- Note that if τ is Prop itself, then the type checker G ... will take care of it.
      if lip
      then 
        do Cn <- mk_fresh_name,
           (Fτ,_) <- using_hammer (hammer_f τ),
           add_axiom Cn Fτ
      else 
        -- Additional check which is not in the paper. If the axiom is of type Prop, we want to add it as statement which must be true. 
        -- Thus, declarations like (Π(x:ℕ) x+x=2*x) are translated by applying F.
        do lip <- lives_in_prop_p c, 
          if lip
          then
            do Cn <- mk_fresh_name,
            (Fc,_) <- using_hammer (hammer_f c),
            add_axiom Cn Fc
          else
            do Cn <- mk_fresh_name,
              (Cc,_) <- using_hammer (hammer_c c),
              (Gcτ,_) <- using_hammer (hammer_g Cc τ),
              add_axiom Cn Gcτ

meta def lambda_expr_to_pi : expr → expr → tactic expr 
| s e@(expr.lam n b a c) := do 
    tactic.trace n, 
    tactic.trace a, 
    tactic.trace c, 
    match c with 
    | cexp@(expr.lam n0 b0 a0 c0) := do
      conv_exp ← lambda_expr_to_pi s cexp,
      return $ expr.pi n b a conv_exp
    | cexp := do
      f ← lambda_expr_to_pi s cexp,
      let pi_e := expr.pi n b a `(f = s),
      return pi_e
    end 
| s e := return e -- All other forms are ignored

meta def process_declarations : list name → hammer_tactic unit
| [] := tactic.skip 
| (x :: xs) := 
    do 
      d ← tactic.get_decl x,
      translate_axiom_expression d.value,
      process_declarations xs

-- TODO: inductive declarations work, but not simple declarations! We get lambda expressions but need pi expression with equality



-- run_cmd do e <- lambda_expr_to_pi `(sum_two) `(λ(x:ℕ),x*2), tactic.trace e

-- match d.value with
--       | expr.lam n b a c := 
--           do
--             tactic.trace n,
--             let e := expr.pi n b a c,
--             translate_axiom_expression e
--       | _ := 

meta def translate_declaration (e : name) : hammer_tactic unit :=
do 
    env <- tactic.get_env,
    d <- tactic.get_decl e,
    l ← tactic.get_eqn_lemmas_for ff e,
    process_declarations (l.append [e])

meta def translate_problem: list name → list expr → hammer_tactic unit
| [] [] := tactic.skip 
| [] (x::xs) := do translate_axiom_expression x, translate_problem [] xs
| (y::ys) xs := do translate_declaration y, translate_problem ys xs

meta def problem_to_format (declr: list name) (clauses: list expr) (conjecture: expr) : hammer_tactic format := 
  do  
    ⟨cl,cl_state⟩ <- using_hammer (translate_problem declr clauses),
    ⟨conj,conj_state⟩ <- using_hammer (hammer_f conjecture),
    return $ to_tptp (hammer_state.axiomas cl_state) conj


--###################
--## Testing stuff ##
--###################

-- == TESTING DECLARATION CONVERSION ==
run_cmd do
  l ← tactic.get_eqn_lemmas_for ff `nat.iterate,
  tactic.trace l

-- def sum_two (x: ℕ) (y: ℕ) : ℕ := x+y

def sum_two : ℕ → ℕ → ℕ
| x y := x + y

def fib : nat -> nat
| 0 := 1
| 1 := 1
| (nat.succ (nat.succ n)) := fib n + fib (nat.succ n)

def fib2 : nat -> nat
| 0 := 1
| 1 := 1
| (nat.succ (nat.succ n)) := sum_two (fib2 n) (fib2 (nat.succ n))

inductive abc
| a : abc
| b (a : abc) : abc

#check nat.iterate.equations._eqn_2
#print prefix nat.iterate.equations._eqn_1
#check tactic.interactive.simp
#check environment
#check tactic.get_env
#check tactic.get_decl
#check declaration
run_cmd do l ← tactic.get_decl `sum, tactic.trace l.value, tactic.trace l.is_definition, l ← tactic.get_eqn_lemmas_for ff `sum_two, tactic.trace l
run_cmd do l ← tactic.get_decl `sum_two, tactic.trace l.value, e ← (lambda_expr_to_pi `(sum_two) l.value), tactic.trace e, ⟨f, _⟩ <- using_hammer $ translate_axiom_expression `(sum_two = λ x y:ℕ, x+y), tactic.trace f, tactic.trace `(sum_two=λ x y : ℕ, x+y)
run_cmd do l ← tactic.get_decl `fib, tactic.trace l.value
run_cmd do process_declarations [`sum_two]
-- run_cmd do a <- tactic.dunfold [`sum_two] `(sum_two), tactic.trace a
-- run_cmd do d <- simp_lemmas.mk_default, l ← tactic.get_decl `sum_two, a <- simp_lemmas.add d l.value, e <- simp_lemmas.rewrite d l.value, tactic.trace e
run_cmd do l ← tactic.get_decl `abc, tactic.trace l.type, tactic.trace l.is_definition, l ← tactic.get_eqn_lemmas_for ff `abc, tactic.trace l

-- == EXAMPLE PROBLEM TRANSLATION ==
run_cmd do ⟨f, _⟩ <- using_hammer $ problem_to_format [`sum_two, `fib] [`(1 : nat), `(1+1 = 2), `(1+2=3), `(fib), `(sum_two 1 2 = 3)] `(not (1+1 = 2)),
           tactic.trace f 
           
-- == TESTING FUNCTION DECLARATION TO EXPRESSION == 

-- We generate somewhere "hammer_c Prop" which breaks. Where do we do that, and how to get around it?
run_cmd do ⟨f,_⟩ <- using_hammer $ problem_to_format [`fib, `sum_two, `fib2] 
                                                     [`(Π(x:ℕ), x + 1 = nat.succ x), `(Π(x y:ℕ),nat.succ x + y = nat.succ (x + y)), `(Π(x y:ℕ),x + y = y + x), `(nat.succ 0 = 1), `(nat.succ 1 = 2), `(nat.succ 2 = 3), `(nat.succ 3 = 4), `(nat.succ 4 = 5), `(nat.succ 5 = 6), `(nat.succ 6 = 7), `(nat.succ 7 = 8), `(0:ℕ), `(1:ℕ), `(2:ℕ), `(3:ℕ), `(4:ℕ), `(5:ℕ), `(6:ℕ), `(7:ℕ), `(8:ℕ)] -- , `(0:ℕ), `(1:ℕ), `(2:ℕ), `(3:ℕ), `(4:ℕ), `(5:ℕ), `(6:ℕ), `(7:ℕ), `(8:ℕ), `(Π x y : ℕ, sum_two x y =x+y)
                                                     `((fib 5 = 8)), 
           tactic.trace f 
--###################
--## IMPORT/EXPORT ##
--###################
open io
open io.fs

meta def export_format (f : format) : io unit := put_str f.to_string

run_cmd do ⟨f,_⟩ <- using_hammer $ problem_to_format [`sum_two, `fib] [`(Π(x:ℕ), x + x = 2 * x), `(2*1 = 2), `(1+2=3), `(1:ℕ), `(2:ℕ)] `((1+1 = 2)),
           let io_output := export_format f,
           let file_handle := mk_file_handle "test.tptp" io.mode.write tt,
           -- let p := write file_handle "test" ,
           tactic.skip


-- =================
-- == OPEN POINTS ==
-- =================
-- 1) Lambda expressions to pi notation to translate them similar to the others. Alternative: convert all function declarations into inductive ones. 
--    Idea from Rob: look into tactic.dsimplify
-- 3) Retrieve all definitions of another definition (example 'def sum_twice (x:ℕ) : ℕ := 2 * square(x)' => get definition of square) and add them to axioms
--    => Ask Rob for old code 
-- 4) IO file export
-- 5) How to translate inductive types
-- 7) Proof reconstruction: get a list of assignments for axiom name (as given to SMT solver) and corresponding expression to know which ones were used

-- == DONE == 2) Inductive declarations use different names. E.g. 'fib' is related to as 'fib._main' in the equations
--    Solution: if we find names with "._" suffix, we just cut them off there (hacky, but might work in most cases). 
-- == DONE == 6) Inductive: exclude previous cases for each constructor. So if 'def fac (n:ℕ) : ℕ | 0 := 0 | n := n * fac (n-1)' is translated, the second case has 'G(n,Nat) ∧ n != 0 → ...' instead of just checking for nat type as 0 fulfills this as well.
