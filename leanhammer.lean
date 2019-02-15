import system.io
import .tptp
import .premise_selection
import .simplification_tptp 
import .translation_tptp
import .problem_translation

--#################
--## System test ##
--#################

-- def sum_two (x: ℕ) (y: ℕ) : ℕ := x+y
-- Inductive declaration because the simple version above is not working yet
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

run_cmd do l ← tactic.get_decl `sum_two, tactic.trace l.value, tactic.trace l.is_definition, l ← tactic.get_eqn_lemmas_for tt `sum_two, d ← tactic.get_decl (list.head l), tactic.trace d.value, (c,_) <- using_hammer $ tactic.infer_type d.value, tactic.trace c
run_cmd do l ← tactic.get_decl `sum_two, tactic.trace l.value, e ← (lambda_expr_to_pi `(sum_two) l.value), tactic.trace e, ⟨f, _⟩ <- using_hammer $ translate_axiom_expression `(sum_two = λ x y:ℕ, x+y), tactic.trace f, tactic.trace `(sum_two=λ x y : ℕ, x+y)
run_cmd do l ← tactic.get_decl `fib, tactic.trace l.value
run_cmd do process_declarations [`sum_two]
-- run_cmd do def_lemmas <- simp_lemmas.mk_default, d ← tactic.get_decl `sum_two, tactic.trace d.value, e <- def_lemmas.dsimplify [`sum_two] d.value, tactic.trace e
-- run_cmd do d <- simp_lemmas.mk_default, l ← tactic.get_decl `sum_two, a <- simp_lemmas.add d l.value, e <- simp_lemmas.rewrite d l.value, tactic.trace e
run_cmd do e <- expr_in_parts `(Π (x:ℕ), x=1), tactic.trace e

run_cmd do l ← tactic.get_decl `abc, tactic.trace l.type, tactic.trace l.is_definition, l ← tactic.get_eqn_lemmas_for ff `abc, tactic.trace l

run_cmd do (contents, features, ⟨n, names⟩) ← get_all_decls,
            tactic.trace $ nearest_k_of_name `sum_two  contents features names 100

-- == SMALL PROBLEM TRANSLATION ==
run_cmd do ⟨f, _⟩ <- using_hammer $ problem_to_format [] [`(Π(x:ℕ), nat.succ x = x + 1), `(1 : nat), `(1+1 = 2)] `(not (1+1 = 2)),
           tactic.trace f 
           
-- == EXAMPLE PROBLEM TRANSLATION == 
run_cmd do ⟨f,_⟩ <- using_hammer $ problem_to_format [`fib2, `sum_two] 
                                                     [`(Π(x:ℕ), x + 1 = nat.succ x), `(Π(x y:ℕ),nat.succ x + y = nat.succ (x + y)), `(Π(x y:ℕ),x + y = y + x), `(nat.succ 0 = 1), `(nat.succ 1 = 2), `(nat.succ 2 = 3), `(nat.succ 3 = 4), `(nat.succ 4 = 5), `(nat.succ 5 = 6), `(nat.succ 6 = 7), `(nat.succ 7 = 8), `(0:ℕ), `(1:ℕ), `(2:ℕ), `(3:ℕ), `(4:ℕ), `(5:ℕ), `(6:ℕ), `(7:ℕ), `(8:ℕ)] -- , `(0:ℕ), `(1:ℕ), `(2:ℕ), `(3:ℕ), `(4:ℕ), `(5:ℕ), `(6:ℕ), `(7:ℕ), `(8:ℕ), `(Π x y : ℕ, sum_two x y =x+y)
                                                     `((fib2 5 = 8)), 
           tactic.trace f 


-- =================
-- == OPEN POINTS ==
-- =================
-- 9) Use typed first-order logic (TF0) as encoding instead of plain FOF in TPTP3
-- 1) Lambda expressions to pi notation to translate them similar to the others. Alternative: convert all function declarations into inductive ones. 
--    Idea from Rob: look into tactic.dsimplify
-- 4) IO file export
-- 5) How to translate inductive types
-- 7) Proof reconstruction: get a list of assignments for axiom name (as given to SMT solver) and corresponding expression to know which ones were used

-- #################
-- ## IN PROGRESS ##
-- #################
-- 3) Retrieve all definitions of another definition (example 'def sum_twice (x:ℕ) : ℕ := 2 * square(x)' => get definition of square) and add them to axioms
--    => Old code moved to Lean 3.3.0. Relevance filter might be implemented externally in C++ to be faster
-- 8) Simplification of terms => VERY FIRST VERSION replacing constant terms by new constant. 
--    Open extensions: -> If a(b, 'nat') and a(b, V1) but 'nat' is the only constant occuring at the second position, we replace this variable by nat
--                     -> Tracable/Understandable constant names for reduced terms (name based on term plus unique prefix)

-- ##########
-- ## DONE ##
-- ##########
-- == DONE == 2) Inductive declarations use different names. E.g. 'fib' is related to as 'fib._main' in the equations
--    Solution: if we find names with "._" suffix, we just cut them off there (hacky, but might work in most cases). 
-- == DONE == 6) Inductive: exclude previous cases for each constructor. So if 'def fac (n:ℕ) : ℕ | 0 := 0 | n := n * fac (n-1)' is translated, the second case has 'G(n,Nat) ∧ n != 0 → ...' instead of just checking for nat type as 0 fulfills this as well.
-- == DONE == 10) Split things into multiple files
