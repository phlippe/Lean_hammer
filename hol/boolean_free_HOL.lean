import .datastructures_hol

meta mutual def hol_type_wo_bool, hol_term_wo_bool, hol_formula_wo_bool
with hol_type_wo_bool : holtype → holtype
| e@(holtype.o) := holtype.ltype "boolean"
| e@(holtype.functor ts t) :=  holtype.functor (list.map (λ (tp : holtype), hol_type_wo_bool tp) ts) (hol_type_wo_bool t)
| e@(holtype.dep_binder ts t) := holtype.dep_binder (list.map (λ (tp : (name × holtype)), (tp.1, hol_type_wo_bool tp.2)) ts) (hol_type_wo_bool t)
| e@(holtype.partial_app t) := holtype.partial_app (hol_term_wo_bool t)
| e := e 

with hol_term_wo_bool: holterm → holterm
| e@(holterm.top) := holterm.const "bool_true"
| e@(holterm.bottom) := holterm.const "bool_false"
| e@(holterm.app t1 t2) := holterm.app (hol_term_wo_bool t1) (hol_term_wo_bool t2)
| e@(holterm.lambda n ty t) := holterm.lambda n (hol_type_wo_bool ty) (hol_term_wo_bool t)
| e := e

with hol_formula_wo_bool: holform → holform 
| e@(holform.P t) := holform.P (hol_term_wo_bool t)
| e@(holform.T t u) := holform.T (hol_term_wo_bool t) (hol_type_wo_bool u)
| e@(holform.eq t u) := holform.eq (hol_term_wo_bool t) (hol_term_wo_bool u)
| e@(holform.neg f) := holform.neg (hol_formula_wo_bool f)
| e@(holform.imp f1 f2) := holform.imp (hol_formula_wo_bool f1) (hol_formula_wo_bool f2)
| e@(holform.iff f1 f2) := holform.iff (hol_formula_wo_bool f1) (hol_formula_wo_bool f2)
| e@(holform.conj f1 f2) := holform.conj (hol_formula_wo_bool f1) (hol_formula_wo_bool f2)
| e@(holform.disj f1 f2) := holform.disj (hol_formula_wo_bool f1) (hol_formula_wo_bool f2)
| e@(holform.all n n1 f) := holform.all n n1 (hol_formula_wo_bool f)
| e@(holform.exist n n1 f) := holform.exist n n1  (hol_formula_wo_bool f)
| e := e


-- meta def axiom_list_wo_bool (l : list axioma) := (list.map (λ (x : axioma), ⟨x.1, hol_formula_wo_bool x.2⟩ ) l)
-- meta def typedef_list_wo_bool (l : list type_def) := (list.map (λ (x : type_def), (x.1, x.2, hol_type_wo_bool x.3)) l)


meta def axiom_list_wo_bool : list axioma → list axioma
| (x :: xs) := [⟨x.1, hol_formula_wo_bool x.2⟩] ++ xs
| [] := []

meta def typedef_list_wo_bool : list type_def → list type_def
| (x :: xs) := [⟨x.1, x.2, hol_type_wo_bool x.3⟩] ++ xs
| [] := []


