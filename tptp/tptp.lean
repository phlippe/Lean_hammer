
@[reducible] meta def debruijn := nat

meta def neg : bool → bool 
| tt := ff
| ff := tt

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

meta def folterm.to_name : folterm → name 
| (folterm.const n) := "c_" ++ n
| (folterm.lconst n1 n2) := "lc_" ++ n1 ++ "_" ++ n2
| (folterm.prf) := "prf"
| (folterm.var n) := "var"
| (folterm.app t u) := "a_" ++ t.to_name ++ "-" ++ u.to_name

-- Check whether a folterm is a constant expression or not (does it contain a variable or not?)
meta def folterm.is_const : folterm → bool
| (folterm.const _) := tt
| (folterm.lconst _ _) := tt
| (folterm.prf) := tt
| (folterm.var _) := ff
| (folterm.app t u) := t.is_const && u.is_const

meta def folterm.is_eq : folterm → folterm → bool 
| (folterm.const n1) (folterm.const n2) := (n1 = n2)
| (folterm.const _) _ := ff 
| (folterm.lconst n1 l1) (folterm.lconst n2 l2) := (n1 = n2) && (l1 = l2)
| (folterm.lconst _ _) _ := ff
| (folterm.prf) (folterm.prf) := tt
| (folterm.prf) _ := ff
| (folterm.var n1) (folterm.var n2) := (n1 = n2)
| (folterm.var _) _ := ff
| (folterm.app t1 u1) (folterm.app t2 u2) := (t1.is_eq t2) && (u1.is_eq u2)
| (folterm.app _ _) _ := ff 

meta def folterm.is_eq_besides_vars : folterm → folterm → bool
| (folterm.var _) _ := tt
| _ (folterm.var _) := tt
| (folterm.const n1) (folterm.const n2) := (n1 = n2)
| (folterm.const _) _ := ff 
| (folterm.lconst n1 l1) (folterm.lconst n2 l2) := (n1 = n2) && (l1 = l2)
| (folterm.lconst _ _) _ := ff
| (folterm.prf) (folterm.prf) := tt
| (folterm.prf) _ := ff
| (folterm.app t1 u1) (folterm.app t2 u2) := (t1.is_eq_besides_vars t2) && (u1.is_eq_besides_vars u2)
| (folterm.app _ _) _ := ff 

meta def folterm.is_eq_besides_deeper_vars : folterm → folterm → bool 
| (folterm.var _) _ := ff
| _ (folterm.var _) := ff
| (folterm.const n1) (folterm.const n2) := (n1 = n2)
| (folterm.const _) _ := ff 
| (folterm.lconst n1 l1) (folterm.lconst n2 l2) := (n1 = n2) && (l1 = l2)
| (folterm.lconst _ _) _ := ff
| (folterm.prf) (folterm.prf) := tt
| (folterm.prf) _ := ff
| (folterm.app t1 u1) (folterm.app t2 u2) := (t1.is_eq_besides_vars t2) && (u1.is_eq_besides_vars u2)
| (folterm.app _ _) _ := ff 

meta def folterm.replace : folterm → folterm → folterm → folterm
| orig@(folterm.app t u) old_term new_term := if orig.is_eq old_term then new_term else folterm.app (folterm.replace t old_term new_term) (folterm.replace u old_term new_term)
| orig old_term new_term := if orig.is_eq old_term then new_term else orig

meta def folform.replace_term : folform → folterm → folterm → folform
| orig@(folform.P t) old_term new_term := folform.P $ t.replace old_term new_term
| orig@(folform.T t1 t2) old_term new_term := folform.T (t1.replace old_term new_term) (t2.replace old_term new_term)
| orig@(folform.eq t1 t2) old_term new_term := folform.eq (t1.replace old_term new_term) (t2.replace old_term new_term)
| orig@(folform.neg f) old_term new_term := folform.neg (f.replace_term old_term new_term)
| orig@(folform.imp f1 f2) old_term new_term := folform.imp (f1.replace_term old_term new_term) (f2.replace_term old_term new_term)
| orig@(folform.iff f1 f2) old_term new_term := folform.iff (f1.replace_term old_term new_term) (f2.replace_term old_term new_term)
| orig@(folform.conj f1 f2) old_term new_term := folform.conj (f1.replace_term old_term new_term) (f2.replace_term old_term new_term)
| orig@(folform.disj f1 f2) old_term new_term := folform.disj (f1.replace_term old_term new_term) (f2.replace_term old_term new_term)
| orig@(folform.all n1 n2 f) old_term new_term := folform.all n1 n2 (f.replace_term old_term new_term)
| orig@(folform.exist n1 n2 f) old_term new_term := folform.exist n1 n2 (f.replace_term old_term new_term)
| orig _ _ := orig

meta def folterm.get_all_const_terms : folterm → list folterm
| c@(folterm.app t u) := if folterm.is_const c then [c] ++ t.get_all_const_terms ++ u.get_all_const_terms else t.get_all_const_terms ++ u.get_all_const_terms
-- All other parts are not considered as constant as we are not interested in replacing a constant by another constant
| (folterm.const _) := []
| (folterm.lconst _ _) := []
| (folterm.prf) := []
| (folterm.var _) := []

meta def folform.get_all_const_terms : folform → list folterm
| orig@(folform.P t) := t.get_all_const_terms
| orig@(folform.T t1 t2) := t1.get_all_const_terms ++ t2.get_all_const_terms
| orig@(folform.eq t1 t2) := t1.get_all_const_terms ++ t2.get_all_const_terms
| orig@(folform.neg f) := f.get_all_const_terms
| orig@(folform.imp f1 f2) := f1.get_all_const_terms ++ f2.get_all_const_terms
| orig@(folform.iff f1 f2) := f1.get_all_const_terms ++ f2.get_all_const_terms
| orig@(folform.conj f1 f2) := f1.get_all_const_terms ++ f2.get_all_const_terms
| orig@(folform.disj f1 f2) := f1.get_all_const_terms ++ f2.get_all_const_terms
| orig@(folform.all n1 n2 f) := f.get_all_const_terms
| orig@(folform.exist n1 n2 f) := f.get_all_const_terms
| orig := []

meta def folterm.contains_only_const : folterm → folterm → bool 
| c@(folterm.app t u) ct := if (c.is_eq_besides_deeper_vars ct) && (neg c.is_const) then ff else t.contains_only_const ct && u.contains_only_const ct
| c ct := (neg (c.is_eq_besides_deeper_vars ct)) || (c.is_const)

meta def folform.contains_only_const : folform → folterm → bool 
| orig@(folform.P t) ct := t.contains_only_const ct
| orig@(folform.T t1 t2) ct := t1.contains_only_const ct && t2.contains_only_const ct
| orig@(folform.eq t1 t2) ct := t1.contains_only_const ct && t2.contains_only_const ct
| orig@(folform.neg f) ct := f.contains_only_const ct
| orig@(folform.imp f1 f2) ct := f1.contains_only_const ct && f2.contains_only_const ct
| orig@(folform.iff f1 f2) ct := f1.contains_only_const ct && f2.contains_only_const ct
| orig@(folform.conj f1 f2) ct := f1.contains_only_const ct && f2.contains_only_const ct
| orig@(folform.disj f1 f2) ct := f1.contains_only_const ct && f2.contains_only_const ct
| orig@(folform.all n1 n2 f) ct := f.contains_only_const ct
| orig@(folform.exist n1 n2 f) ct := f.contains_only_const ct
| orig ct := tt

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

meta instance : has_to_format folform :=
⟨folform.to_format⟩

-- Convert formula with name and role to output string
meta def to_fof : string → role → folform → format
| id r f :=
to_fmt "fof("
++ (mygroup $ nest 4 $ join $ list.intersperse ("," ++ line) $ -- Combine all parts by "," and new line
  [to_fmt id, to_fmt r, "(" ++ (mygroup $ nest 1 $ to_fmt f) ++ ")"]) ++ to_fmt ")." -- Output: fof(name, role, (formula)).
  
-- Combine list of axioma into single string
meta def export_formula : list axioma → folform → format
| (⟨n, f⟩::as) conjecture := 
  to_fof ("'" ++ to_string n ++ "'") role.axioma f
     ++ line
     ++ line
     ++ export_formula as conjecture
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

------------------------------------
------------------------------------

meta def example_formula : folform :=
folform.all `h1 `h1 $ folform.all `h2 `h2 $ -- folform.all `h3 `h3 $ 
  folform.neg $
  folform.iff
    (folform.conj
      (folform.neg $ folform.eq (folterm.var 0) (folterm.var 1)) 
      (folform.eq (folterm.var 0) (folterm.var 1)) )
    (folform.imp
      (folform.conj (folform.P $ folterm.const "a") (folform.disj (folform.P $ folterm.var 0) (folform.P $ folterm.var 1)))
      (folform.T (folterm.var 0) (folterm.app (folterm.var 1) (folterm.var 0))))

meta def example_formula2 : folform :=
folform.imp (folform.conj (folform.P $ folterm.const "n") (folform.P $ folterm.const "a"))
(folform.T (folterm.const "n") (folterm.app (folterm.const "n") (folterm.app (folterm.const "n") (folterm.const("a")))))

meta def print_list : list folterm → tactic unit
| (x :: xs) := do print_list xs, tactic.trace $ x.to_format 1 
| [] := tactic.skip

-- run_cmd do let t1 := folterm.app (folterm.const "a") (folterm.var 1), let t2 := folterm.app (folterm.const "a") (folterm.var 1), tactic.trace $ t1.is_eq t2
-- run_cmd do let t1 := folterm.app (folterm.var 2) (folterm.const "a"), let t2 := folterm.app (folterm.const "a") (folterm.const "d"), 
--            tactic.trace $ t1.is_eq_besides_vars t2, 
--            tactic.trace $ t1.contains_only_const t2,
--            tactic.trace $ (folterm.var 2).contains_only_const t2
-- run_cmd do let form := example_formula2, 
--            let t1 := folterm.app (folterm.const "n") (folterm.const "a"), 
--            let t2 := folterm.const "n2", 
--            tactic.trace $ t1.to_format 1, 
--            tactic.trace $ t2.to_format 1, 
--            tactic.trace form, 
--            tactic.trace $ folform.replace_term form t1 t2,
--            print_list $ folform.get_all_const_terms form,
--            print_list $ folform.get_all_const_terms $ folform.replace_term form t1 t2

-- #eval tactic.trace $ to_fof "example_formula" role.axioma example_formula  
-- #eval tactic.trace $ to_fof "example_formula2" role.conjecture example_formula2  
-- #eval tactic.trace example_formula.repr 

-----------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------
