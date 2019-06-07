meta mutual inductive holtype, holterm 
with holtype : Type
| o : holtype -- Boolean (predefined TFF $o) 
| i : holtype -- Individual (predefined TFF $i, default type)
| int : holtype -- Individual (predefined TFF $int, integer)
| rat : holtype -- Individual (predefined TFF $rat, rational numbers)
| real : holtype -- Individual (predefined TFF $real, real numbers)
| type : holtype -- Type (predefined TFF $tType)
| ltype : name → holtype -- Self-specified type
| functor : list holtype → holtype → holtype 
-- binder !> in HOL (example: !>[A: $tType, B: $tType] : ((map@A@B) > A > B))  where map : $tType > $tType > $tType
| dep_binder : list (name × holtype) → holtype → holtype -- We only encode !>[A: $tType, B: $tType] by the first list. Afterwards, it can be any holtype
-- Should for example encode "map@A@B" as stated above
| partial_app : holterm → holtype

-- Problem: dependencies to each other...
with holterm : Type
| const : name → holterm -- Constant with given label
| lconst : name → holtype → holterm -- Second term should rather by holtype
| prf : holterm
| var : nat → holterm -- Variables just specified by counter: X1,X2,X3,...
| app : holterm → holterm → holterm -- @(t,s) is the same as t s => apply t on input s
-- Encode λ-expressions explicitly
| lambda : name → holtype → holterm → holterm
-- Pi expression should not be necessary/implemented in TH1?
-- | pi : nat → holtype → holterm → holterm
-- Boolean constant
| top : holterm
| bottom : holterm

meta inductive holform
| P : holterm → holform -- Provability of a term (used in e.g. hammer_f if expression does not fit to any other option)
| T : holterm → holtype → holform -- Encoding of term constraints
| eq : holterm → holterm → holform -- Equality. t == s
| bottom : holform -- Constant False
| top : holform -- Constant True
| neg : holform → holform -- Negation function. ¬A
| imp : holform → holform → holform -- Imply: A → B
| iff : holform → holform → holform -- Two-sided imply/iff: A ↔ B
| conj : holform → holform → holform -- Conjunction: A ∧ B
| disj : holform → holform → holform -- Disjunction: A ∨ B
| all : name → holtype → holform → holform -- For all: ∀ (a : α) t -- a is the name of the parameter/variable, α the type, t the formula 
| exist : name → holtype → holform → holform -- Exists: ∃ (a : α) t -- Similar as above


meta structure introduced_constant := -- Structure representing a new constant introduced for translation
(n : name) (e : expr) -- name and type

meta structure axioma := -- Note: axiom is reserved word in Lean, thus the additional a
(n : name) (f : holform) -- Every axiom is specified by a name and its formula

meta structure type_def := 
(def_name : name) (type_name : name) (t : holtype)

meta inductive role -- Role of a formula. Can be either axiom, definition or conjecture
| axioma : role
| r_definition : role -- Keyword "definition" already used in Lean
| conjecture : role

meta def role.to_format : role → format
| role.axioma := to_fmt "axiom"
| role.r_definition := to_fmt "definition"
| role.conjecture := to_fmt "conjecture"

meta structure hammer_state := -- Structure representing the state of the hammer (list of axioms with corresponding list of newly introduced constants for translation)
(axiomas : list axioma)
(type_definitions : list type_def)
(introduced_constants : list introduced_constant)

meta def hammer_tactic :=
state_t hammer_state tactic

meta def holterm.abstract_locals_core : holterm → ℕ → list name → holterm
| e@(holterm.lconst n n1) d ln :=
  list.foldl
    (λ e' n', if n = n' then holterm.var $ d + ln.reverse.find_index (= n) else e')
    e
    ln
| (holterm.app t1 t2) d ln := holterm.app (t1.abstract_locals_core d ln) (t2.abstract_locals_core d ln)
-- | e@(holterm.lambda n t1 )
| e d ln := e

meta def holterm.abstract_locals : holterm → list name → holterm := λ f l, f.abstract_locals_core 0 l

meta def holform.abstract_locals_core : holform → nat → list name → holform
| e@(holform.P t) d ln := holform.P $ t.abstract_locals_core d ln
| e@(holform.T t u) d ln := e
| e@(holform.eq t u) d ln := holform.eq (t.abstract_locals_core d ln) (u.abstract_locals_core d ln)
| e@(holform.neg f) d ln := holform.neg (f.abstract_locals_core d ln)
| e@(holform.imp f1 f2) d ln := holform.imp (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(holform.iff f1 f2) d ln := holform.iff (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(holform.conj f1 f2) d ln := holform.conj (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(holform.disj f1 f2) d ln := holform.disj (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(holform.all n n1 f) d ln := holform.all n n1 (f.abstract_locals_core (d+1) ln)
| e@(holform.exist n n1 f) d ln := holform.exist n n1 (f.abstract_locals_core (d+1) ln)
| e d ln := e

meta def holform.abstract_locals : holform → list name → holform := λ f l, f.abstract_locals_core 0 l

meta mutual def holtype_list_to_repr, holtype_cross_list_to_repr, holtype.repr, holterm.repr
with  holtype_list_to_repr : list holtype → string 
| (x :: xs) := x.repr ++ " " ++ (holtype_list_to_repr xs)
| [] := ""

with  holtype_cross_list_to_repr : list (name × holtype) → string 
| ((n,x) :: xs) := name.to_string n ++ ":" ++ x.repr ++ " " ++ (holtype_cross_list_to_repr xs)
| [] := ""

with holtype.repr : holtype → string 
| e@(holtype.o) := "(holtype.o)"
| e@(holtype.i) := "(holtype.i)"
| e@(holtype.int) := "(holtype.int)"
| e@(holtype.rat) := "(holtype.rat)"
| e@(holtype.real) := "(holtype.real)"
| e@(holtype.type) := "(holtype.type)"
| e@(holtype.ltype n) := "(holtype.ltype " ++ name.to_string n ++ ")"
| e@(holtype.functor ts t) := "(holtype.functor [" ++  holtype_list_to_repr ts ++ "] " ++ t.repr ++ ")"
| e@(holtype.dep_binder ts t) := "(holtype.dep_binder [" ++ holtype_cross_list_to_repr ts ++ "] " ++ t.repr ++ ")"
| e@(holtype.partial_app t) := "(holtype.partial_app " ++ t.repr ++ ")"

with holterm.repr : holterm → string
| e@(holterm.const n) := "(holterm.constant " ++ name.to_string n ++ ")"
| e@(holterm.lconst n t) := "(holterm.local_const " ++ name.to_string n ++ holtype.repr t ++ ")"
| e@(holterm.prf) := "(holterm.prf)"
| e@(holterm.var n) := "(holterm.var " ++ repr n ++ ")"
| e@(holterm.app t1 t2) := "(holterm.app " ++ holterm.repr t1 ++ " " ++ holterm.repr t2 ++ ")"
-- Encode λ-expressions explicitly
| e@(holterm.lambda n ty t) := "(holterm.lambda " ++ name.to_string n ++ " " ++ holtype.repr ty ++ " " ++ holterm.repr t ++ ")"
-- | e@(holterm.pi n ty t) := "(holterm.pi " ++ repr n ++ " " ++ holtype.repr ty ++ " " ++ holterm.repr t ++ ")"
-- Boolean constant
| e@(holterm.top) := "(holterm.top)"
| e@(holterm.bottom) := "(holterm.bottom)"

meta def holform.repr : holform → string
| e@(holform.P t) := "(holform.P " ++ t.repr ++ ")"
| e@(holform.T n t) := "(holform.T " ++ holterm.repr n ++ holtype.repr t ++ ")"
| e@(holform.eq t1 t2) := "(holform.eq " ++ t1.repr ++ t2.repr ++ ")"
-- Boolean constant
| e@(holform.bottom) := "(holform.bottom)"
| e@(holform.top) := "(holform.top)"
| e@(holform.neg f) := "(holform.neg " ++ f.repr ++ ")"
| e@(holform.imp f1 f2) := "(holform.imp " ++ f1.repr ++ " " ++ f2.repr ++ ")"
| e@(holform.iff f1 f2) := "(holform.iff " ++ f1.repr ++ " " ++ f2.repr ++ ")"
| e@(holform.conj f1 f2) := "(holform.conj " ++ f1.repr ++ " " ++ f2.repr ++ ")"
| e@(holform.disj f1 f2) := "(holform.disj " ++ f1.repr ++ " " ++ f2.repr ++ ")"
| e@(holform.all n t f) := "(holform.all " ++ name.to_string n ++ " " ++ t.repr  ++ " " ++ f.repr ++ ")"
| e@(holform.exist n t f) := "(holform.exist " ++ name.to_string n ++ " " ++ t.repr ++ " " ++ f.repr ++ ")"

meta mutual def holtype_list_to_format, holtype_cross_list_to_format, holtype.to_format_aux, holterm.to_format_aux
with  holtype_list_to_format : list holtype → ℕ → ℕ → string → format 
| (x :: xs) depth n c := if n > 0
                   then " " ++ c ++ " " ++ x.to_format_aux depth ++ (holtype_list_to_format xs depth (n+1) c)
                   else x.to_format_aux depth ++ (holtype_list_to_format xs depth (n+1) c)
| [] depth n c := ""

with  holtype_cross_list_to_format : list (name × holtype) → ℕ → ℕ → string → format 
| ((na,x) :: xs) depth n c := if n > 0
                   then " " ++ c ++ " " ++ to_fmt na ++ ": " ++ x.to_format_aux depth ++ (holtype_cross_list_to_format xs depth (n+1) c)
                   else to_fmt na ++ ": " ++ x.to_format_aux depth ++ (holtype_cross_list_to_format xs depth (n+1) c)
| [] depth n c := ""

with holtype.to_format_aux : holtype → ℕ → format 
| e@(holtype.o) _ := "$o"
| e@(holtype.i) _ := "$i"
| e@(holtype.int) _ := "$int"
| e@(holtype.rat) _ := "$rat"
| e@(holtype.real) _ := "$real"
| e@(holtype.type) _ := "$tType"
| e@(holtype.ltype n) _ := to_fmt n
| e@(holtype.functor ts t) depth :=  (holtype_list_to_format ts depth 0 ">") ++ " > " ++ t.to_format_aux depth
| e@(holtype.dep_binder ts t) depth := "!>[" ++ holtype_cross_list_to_format ts depth 0 "," ++ "] : (" ++ t.to_format_aux depth ++ ")"
| e@(holtype.partial_app t) depth := "(" ++ t.to_format_aux depth ++ ")"

with holterm.to_format_aux : holterm → ℕ → format 
| e@(holterm.const n) _ := to_fmt n
| e@(holterm.lconst n _) _ := to_fmt n
| e@(holterm.prf) _ := "prf"
| e@(holterm.var n) depth := "V" ++ to_fmt (depth - n)
| e@(holterm.app t1 t2) depth := "(" ++ t1.to_format_aux depth ++ "@" ++ t2.to_format_aux depth ++ ")"
| e@(holterm.lambda n ty t) depth := "( ^[" ++ to_fmt n ++ ":" ++ ty.to_format_aux depth ++ "] : " ++ t.to_format_aux (depth + 1) ++ " )"
-- Boolean constant
| e@(holterm.top) _ := "$true"
| e@(holterm.bottom) _ := "$false"

meta def holform.to_format_aux : holform → ℕ → format
| e@(holform.P t) depth := "p(" ++ t.to_format_aux depth ++ ")"
| e@(holform.T n t) depth := "t(" ++ n.to_format_aux depth ++ t.to_format_aux depth ++ ")"
| e@(holform.eq t1 t2) depth := "(" ++ t1.to_format_aux depth ++ "=" ++ t2.to_format_aux depth ++ ")"
-- Boolean constant
| e@(holform.bottom) _ := to_fmt "$false"
| e@(holform.top) _ := to_fmt "$true"
| e@(holform.neg f) depth := "~(" ++ f.to_format_aux depth ++ ")"
| e@(holform.imp f1 f2) depth := "(" ++ f1.to_format_aux depth ++ " => " ++ f2.to_format_aux depth ++ ")"
| e@(holform.iff f1 f2) depth := "(" ++ f1.to_format_aux depth ++ " <=> " ++ f2.to_format_aux depth ++ ")"
| e@(holform.conj f1 f2) depth := "(" ++ f1.to_format_aux depth ++ " & " ++ f2.to_format_aux depth ++ ")"
| e@(holform.disj f1 f2) depth := "(" ++ f1.to_format_aux depth ++ " | " ++ f2.to_format_aux depth ++ ")"
| e@(holform.all n t f) depth := "! [" ++ to_fmt n ++ ":" ++ t.to_format_aux depth ++ "] : " ++ f.to_format_aux (depth + 1)
| e@(holform.exist n t f) depth := "? [" ++ to_fmt n ++ ":" ++ t.to_format_aux depth ++ "] : " ++ f.to_format_aux (depth + 1)


meta def holtype.to_format (t : holtype) : format := t.to_format_aux 0 
meta def holterm.to_format (t : holterm) : format := t.to_format_aux 0 
meta def holform.to_format (f : holform) : format := f.to_format_aux 0 

meta def holterm.to_name : holterm → name 
| e := e.to_format.to_string

meta def holtype.to_name : holtype → name 
| e := e.repr
-- Convert formula with name and role to output string
meta def axiom_to_thf (id : string) (r : role) (f : holform) : format :=
    to_fmt "thf(" ++ to_fmt id ++ "," ++ r.to_format ++ ",(" ++ f.to_format ++ "))."
  
-- Convert formula with name and role to output string
meta def typedef_to_thf (id : string) (type_name : name) (t : holtype) : format :=
    to_fmt "thf(" ++ to_fmt id ++ ",type,(" ++ to_fmt type_name ++ " : " ++ t.to_format ++ "))."
  
-- Combine list of axioma, type definitions and conjecture into single string
meta def export_formula : list type_def → list axioma → holform → format
| (⟨def_n, type_n, t⟩::tds) axiomas conjectures := 
  typedef_to_thf ("'" ++ to_string def_n ++ "'") type_n t
     ++ "\n\n"
     ++ export_formula tds axiomas conjectures
| [] (⟨n, f⟩::as) conjecture := 
  axiom_to_thf ("'" ++ to_string n ++ "'") role.axioma f
     ++ "\n\n"
     ++ export_formula [] as conjecture
| [] [] conjecture := axiom_to_thf "'problem_conjecture'" role.conjecture conjecture

---------------------
-- DEBUG FUNCTIONS --
---------------------
meta def example_formula : holform :=
holform.all `test (holtype.ltype `myType) $ 
    holform.eq
        (holterm.app (holterm.app (holterm.const `h1) (holterm.const `h2)) (holterm.const `test))
        (holterm.var 1)

meta def example_type : holtype :=
holtype.dep_binder [(`A, holtype.o), (`B, holtype.i)] $
    holtype.functor [holtype.partial_app (holterm.app (holterm.const `map) (holterm.const `A)), holtype.ltype `B] holtype.type

meta def example_axiom : axioma := ⟨`test_axiom, example_formula⟩
meta def example_type_def : type_def := ⟨`test_type_def, `myType, example_type⟩

run_cmd do tactic.trace example_formula.to_format
run_cmd do tactic.trace example_type.to_format
run_cmd do tactic.trace $ export_formula [example_type_def] [example_axiom] example_formula