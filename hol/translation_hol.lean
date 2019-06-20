import .datastructures_hol

meta instance : monad hammer_tactic :=
state_t.monad 

meta instance (α : Type) : has_coe (tactic α) (hammer_tactic α) :=
⟨state_t.lift⟩


meta def using_hammer {α} (t : hammer_tactic α) : tactic (α × hammer_state) :=
do let ss := hammer_state.mk [] [] [],
   state_t.run t ss 

meta def when' (c : Prop) [decidable c] (tac : hammer_tactic unit) : hammer_tactic unit :=
if c then tac else tactic.skip

meta def lives_in_prop_p (e : expr) : hammer_tactic bool :=
do tp ← tactic.infer_type e,
   return (if eq tp (expr.sort level.zero) then tt else ff)

meta def lives_in_type (e : expr) : hammer_tactic bool :=
do tp ← tactic.infer_type e,
   return (if eq tp (expr.sort (level.succ (level.succ level.zero))) then tt else ff)

meta def add_axiom (n : name) (axioma : holform) : hammer_tactic unit :=
do state_t.modify (fun state, {state with axiomas := ⟨n, axioma⟩ :: state.axiomas})

meta def add_type_def (def_name : name) (type_name : name) (t : holtype) : hammer_tactic unit :=
do state_t.modify (fun state, {state with type_definitions := ⟨def_name, type_name, t⟩ :: state.type_definitions})

meta def add_constant (n : name) (e : expr) : hammer_tactic unit :=
do state_t.modify (fun state, {state with introduced_constants := ⟨n, e⟩ :: state.introduced_constants })

-- TODO: Check type for being unique/defined! 
-- meta def is_type_defined (type : holtype) : bool := list_contains_type 

-- meta def list_contains_type : list type_def → holtype → bool 
-- | (c :: cs) t := ff || list_contains_type cs t
-- | [] t := ff

meta def holtype.from_name : name → holtype 
| "$o" := holtype.o 
-- | "bool" := holtype.o  -- TODO: Check the expression name for a boolean!
| "$i" := holtype.i 
| "$tType" := holtype.type 
| s := holtype.ltype s 
-- TODO: Integrate a mechanism for adding the new local type as type into tactic state

meta def holtype.infer_type : holterm → tactic holtype
| (holterm.const n) := return (holtype.ltype n) -- TODO: Check for "n" in type definitions. If in there, use found type. Otherwise, add it with type $i
| (holterm.lconst n n1) := return n1
| (holterm.prf) := return holtype.o
| (holterm.var n) := return holtype.i -- TODO: Infer types of variables in holterms
| (holterm.app t u) := return holtype.i -- TODO: Infer type for application (application is probably a function defined as "tff(application, type, a : ($i * $i) > $i)", but we know the type of some specific applications...)
| _ := return holtype.i 

meta def holtype.from_expr : expr → holtype 
| e@(expr.const n _) := holtype.ltype n 
| e := holtype.i

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
                    

meta def var_list_to_type_list : list (name × name × expr) → list (name × holtype × expr)
| ((n, n1, t) :: xs) := (n, holtype.from_name n1, t) :: var_list_to_type_list xs
| [] := []

-- FC(Γ;Πx:t.s): List of free variables in expression excluding x in s
meta def hammer_fc (e: expr) : list $ name × holtype × expr :=
var_list_to_type_list $ 
expr.fold e []
  (λ (e : expr) n l, 
    match e with
    | e@(expr.local_const n n1 _ t) := let e := (n, n1, t) in if e ∉ l then e::l else l
    | _ := l
    end)

-- Set of free variables that are not Γ proofs
meta def hammer_ff (l : list $ name × holtype × expr) : hammer_tactic $ list $ name × holtype :=
do  exprs ← list.mfilter
      (λ x, let (⟨_, _, t⟩ : name × holtype × expr) := x in
        do  lip ← lives_in_prop_p t,
            return ¬lip)
      l, 
    return $ list.foldl
      (λ a (x : name × holtype × expr), let (⟨n, n1, t⟩ : name × holtype × expr) := x in
        ⟨n, n1⟩ :: a)
      [] exprs 

meta def wrap_quantifier (binder : name → holtype → holform → holform) (ns : list $ name × holtype) (f : holform) : holform :=
list.foldr
  (λ (np : name × holtype) f, binder np.1 np.2 f)
  (holform.abstract_locals f (list.map (λ (np : name × holtype), np.1) ns))
  ns      

meta def collect_lambdas_aux :
    (expr × (list $ name × holtype × expr)) → 
    hammer_tactic (expr × (list $ name × holtype × expr))
| (e@(expr.lam n n1 t _), l) := do (b, xn) ← body_of e, tactic.trace b, tactic.trace xn, collect_lambdas_aux (b, (xn, holtype.from_expr t, t) :: l)
| a := return a

meta def remove_suffix_of_string : list char → list char 
| ['.','_','m','a','i','n'] := []
-- | ('.' :: '_' :: b) := [] -- What about other suffixes than main?
| (a :: b) := ([a] ++ remove_suffix_of_string b)
| [] := []

meta def collect_lambdas (e : expr) := collect_lambdas_aux (e, [])

meta def trace_list : list (name × holtype) → hammer_tactic unit
| (x :: xs) := do tactic.trace (x.1), trace_list xs
| _ := tactic.trace "End"


meta mutual def hammer_c_aux, hammer_g_aux, hammer_f_aux
with hammer_c_aux : expr → ℕ → hammer_tactic holterm
| e@(expr.const n _) _ := 
  do 
    t ← tactic.infer_type e, -- consult the environment (get type of expression)
    lip ← lives_in_prop_p t, -- check whether t is prop or not
    if lip
    then
      return $ holterm.prf -- What about the type/formula it actually proofs?
    else
      return $ holterm.const $ (remove_suffix_of_string n.to_string.to_list).as_string 
| (expr.local_const n pp _ t) depth := -- Same for local constants
  do  lip ← lives_in_prop_p t,
      if lip
      then
        return $ holterm.prf
      else
        do  ttype ← (hammer_g_aux t depth),
            return $ holterm.lconst n ttype
| (expr.app t s) depth := -- Application (in paper C_Γ(ts)=...)
  do  tp ← hammer_c_aux t depth, -- Get C_Γ(t)
      sp ← hammer_c_aux s depth, -- Get C_Γ(s)
      match tp with
      | holterm.prf := return holterm.prf -- If C_Γ(t) is type proof, then just return type proof
      | _ := -- Anything else: check what type C_Γ(s) has
        match sp with
        | holterm.prf := return tp -- If it is a proof, return C_Γ(t)
        | _ := return $ holterm.app tp sp -- else: Return C_Γ(t) applied on C_Γ(s)
        end
      end

| e@(expr.pi n n1 t _) depth := -- Dependent types
  do sorry -- TODO: How to deal with pi expressions the best?

| e@(expr.lam n b a c) depth := -- Lambda expression C_Γ(λx:τ.t)=Fy_0
  do  -- tactic.trace "Lambda at depth ",
      let vname := "V" ++ to_string depth,
      -- tactic.trace vname,
      vtype <- hammer_g_aux a depth, -- Type of variable
      inner_expr <- hammer_c_aux c (depth+1), -- Expression within the lambda expression
      return $ holterm.lambda vname vtype inner_expr

| e@(expr.var n) depth := return $ holterm.var n 
-- TODO: Check if those need to be implemented as well
| e@(expr.elet x τ t s) depth := do tactic.trace "Found elet during translation",
                           undefined
| e@(expr.sort _) depth := do tactic.trace "Found sort during translation", 
                     undefined
| e@(expr.mvar _ _ _) depth := do tactic.trace "Found mvar during translation",  
                         undefined
| e@(expr.macro _ _) depth := do tactic.trace "Found macro during translation", 
                        undefined

with hammer_g_aux : expr → ℕ → hammer_tactic holtype
| `(ℕ) _ := return holtype.int
| `(expr.sort level.zero) _ := return holtype.o
| `(Sort _) _ := return holtype.type
| e@(expr.app a b) depth := do 
                    transl_a <- hammer_c_aux a depth,
                    transl_b <- hammer_c_aux b depth,
                    return $ holtype.partial_app $ holterm.app transl_a transl_b
| e@(expr.lam n b a c) depth := do 
                    let vname := "V" ++ to_string depth,
                    vtype <- hammer_g_aux a depth, -- Type of variable
                    inner_expr <- hammer_g_aux c (depth+1), -- Expression within the lambda expression
                    match inner_expr with 
                    | holtype.dep_binder l t := return $ holtype.dep_binder ([(vname, vtype)]++l) t
                    | _ := return $ holtype.dep_binder [(vname, vtype)] inner_expr
                    end
-- Equal to Π equation
| `(%%l → %%r) depth := do 
                    right_type <- hammer_g_aux r depth,
                    left_type <- hammer_g_aux l depth,
                    match right_type with 
                    | holtype.functor list_params return_type := return $ holtype.functor ([left_type] ++ list_params) return_type
                    | _ := return $ holtype.functor [left_type] right_type
                    end
| e@(expr.const n _) _ := return $ holtype.ltype e.to_string
| e depth := do tactic.trace "hammer_g_aux expression Type", tactic.trace e, return $ holtype.i

with hammer_f_aux : expr → ℕ → hammer_tactic holform
-- Pi notations are translated as ∀x
| e@(expr.pi n _ t s) depth :=
  do  lip ← lives_in_prop_p t,
      if lip -- If t is prop, we can translate it more efficiently (t → s)
      then
        do  fe1 ← hammer_f_aux t depth,
            (s, _) ← body_of e,
            fe2 ← hammer_f_aux s depth,
            return $ holform.imp fe1 fe2
      else
        do  let vname := "V" ++ to_string depth,
            vtype <- hammer_g_aux t depth, -- Type of variable
            fe2 ← hammer_f_aux s (depth+1),
            return $ holform.all vname vtype fe2
-- Translating conjunction
| e@`(and %%t %%s) depth :=
  do  fe1 ← hammer_f_aux t depth,
      fe2 ← hammer_f_aux s depth,
      return $ holform.conj fe1 fe2
-- Translating disjunction
| `(or %%t %%s) depth :=
  do  fe1 ← hammer_f_aux t depth,
      fe2 ← hammer_f_aux s depth,
      return $ holform.disj fe1 fe2
-- Translating two-sided implication A⇄B
| `(iff %%t %%s) depth :=
  do  fe1 ← hammer_f_aux t depth,
      fe2 ← hammer_f_aux s depth,
      return $ holform.iff fe1 fe2   
-- Translating negation                    
| `(not %%t) depth :=
  do  fe1 ← hammer_f_aux t depth,
      return $ holform.neg $ fe1  
-- Translating equality
| `(%%t = %%s) depth :=
  do  fe1 ← hammer_c_aux t depth,
      fe2 ← hammer_c_aux s depth,
      return $ holform.eq fe1 fe2                                                    
| t  depth :=
  do  ge1 ← hammer_c_aux t depth,
      return $ holform.P ge1

meta def hammer_f (e : expr) : hammer_tactic holform := hammer_f_aux e 1
meta def hammer_c (e : expr) : hammer_tactic holterm := hammer_c_aux e 1
meta def hammer_g (e : expr) : hammer_tactic holtype := hammer_g_aux e 1
-- def add_type_constraint (n : name) (e : expr) : hammer_tactic unit :=
-- do
--   tp ← tactic.infer_type e,
--   type_expr ← hammer_g_aux tp 1,
--   add_axiom

---------------------
-- DEBUG FUNCTIONS --
---------------------

run_cmd do (c, _) <- using_hammer $ hammer_c_aux `(1+1=2) 1, tactic.trace $ holterm.to_format c
run_cmd do (c, _) <- using_hammer $ hammer_c_aux `(λ (x:ℕ→ℕ), x 1 + 1 = (λ(y:ℕ), (x 1)-y*1) 1 ) 1, tactic.trace $ holterm.to_format c
run_cmd do (c, _) <- using_hammer $ hammer_c_aux `(λ (x:(list ℕ)→ℕ), 1) 1, tactic.trace $ holterm.to_format c
run_cmd do (c, _) <- using_hammer $ hammer_c_aux `(λ {α : Type} (x:(list α)→ℕ), 1) 1, tactic.trace $ holterm.to_format c


def fib : nat -> nat
| 0 := 1
| 1 := 1
| (nat.succ (nat.succ n)) := fib n + fib (nat.succ n)


run_cmd do (c, _) <- using_hammer $ hammer_f_aux `(1+1=2) 1, tactic.trace $ holform.to_format c
run_cmd do (c, _) <- using_hammer $ hammer_g_aux `(fib) 1, tactic.trace $ holtype.to_format c
run_cmd do tp ← tactic.infer_type `(fib), (c, _) <- using_hammer $ hammer_g_aux tp 1, tactic.trace $ holtype.to_format c
