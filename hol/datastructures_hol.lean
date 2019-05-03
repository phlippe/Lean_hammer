

meta inductive holtype 
| o : holtype -- Boolean (predefined TFF $o) 
| i : holtype -- Individual (predefined TFF $i, default type)
| type : holtype -- Type (predefined TFF $tType)
| ltype : name → holtype -- Self-specified type
| functor : list holtype → holtype → holtype 
-- binder !> in HOL (example: !>[A: $tType, B: $tType] : ((map@A@B) > A > B))  where map : $tType > $tType > $tType
| dep_binder : list holtype → holtype → holtype -- We only encode !>[A: $tType, B: $tType] by the first list. Afterwards, it can be any holtype
-- Necessary? Should for example encode "map@A@B" as stated above
| partial_app : name → holtype

-- Problem: dependencies to each other...
meta inductive holterm
| const : name → holterm -- Constant with given label
| lconst : name → holtype → holterm -- Second term should rather by holtype
| prf : holterm
| var : nat → holterm -- Variables just specified by counter: X1,X2,X3,...
| app : holterm → holterm → holterm -- @(t,s) is the same as t s => apply t on input s
-- Encode λ-expressions explicitly
| lambda : nat → holtype → holterm → holterm
| pi : nat → holtype → holterm → holterm
-- Boolean constant
| top : holterm
| bottom : holterm

meta inductive holform
| P : holterm → holform
| T : name → holtype → holform
| eq : holterm → holterm → holform -- Equality. t == s
| bottom : holform -- Constant False
| top : holform -- Constant True
| neg : holform → holform -- Negation function. ¬A
| imp : holform → holform → holform -- Imply: A → B
| iff : holform → holform → holform -- Two-sided imply/iff: A ↔ B
| conj : holform → holform → holform -- Conjunction: A ∧ B
| disj : holform → holform → holform -- Disjunction: A ∨ B
| all : name → holtype → holform → holform -- For all: ∀ (a : α) t -- a and α are the names, t the formula 
| exist : name → holtype → holform → holform -- Exists: ∃ (a : α) t -- Similar as above


meta structure introduced_constant := -- Structure representing a new constant introduced for translation
(n : name) (e : expr) -- name and type

meta structure axioma := -- Note: axiom is reserved word in Lean, thus the additional a
(n : name) (f : holform) -- Every axiom is specified by a name and its formula

meta structure hammer_state := -- Structure representing the state of the hammer (list of axioms with corresponding list of newly introduced constants for translation)
(axiomas : list axioma)
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

meta def holtype.repr : holtype → string 
| t := "Test"

meta def holterm.repr : holterm → string
| e@(holterm.const n) := "(holterm.constant " ++ name.to_string n ++ ")"
| e@(holterm.lconst n t) := "(holterm.local_const " ++ name.to_string n ++ holtype.repr t ++ ")"
| e@(holterm.prf) := "(holterm.prf)"
| e@(holterm.var n) := "(holterm.var " ++ repr n ++ ")"
| e@(holterm.app t1 t2) := "(holterm.app " ++ holterm.repr t1 ++ " " ++ holterm.repr t2 ++ ")"
-- Encode λ-expressions explicitly
| e@(holterm.lambda n ty t) := "(holterm.lambda " ++ repr n ++ " " ++ holtype.repr ty ++ " " ++ holterm.repr t ++ ")"
| e@(holterm.pi n ty t) := "(holterm.pi " ++ repr n ++ " " ++ holtype.repr ty ++ " " ++ holterm.repr t ++ ")"
-- Boolean constant
| e@(holterm.top) := "(holterm.top)"
| e@(holterm.bottom) := "(holterm.bottom)"