import .tptp
import .translation_tptp

--####################
--## Simplification ##
--####################

meta def replace_term_in_list : list axioma → folterm → folterm → list axioma
| (x :: xs) old_term new_term := [⟨x.n, folform.replace_term x.f old_term new_term⟩] ++ (replace_term_in_list xs old_term new_term)
| [] old_term new_term := []

meta def replace_term_in_formlist : list folform → folterm → folterm → list folform
| (x :: xs) old_term new_term := [folform.replace_term x old_term new_term] ++ (replace_term_in_formlist xs old_term new_term)
| [] old_term new_term := []

meta def is_term_const_in_list : list axioma → folterm → bool
| (x :: xs) t := folform.contains_only_const x.f t && is_term_const_in_list xs t
| [] t := tt

-- these aren't really tactics
meta def check_for_replacement : list folterm → list folform → list axioma → folform → bool → (bool × list folform × list axioma × folform)
| (x :: xs) ds clauses conj bf :=
      let x_const := (is_term_const_in_list clauses x) && (folform.contains_only_const conj x) in
      if x_const
      then
        let c_name := x.to_name, -- mk_fresh_name
            new_const_term := folterm.const ("const_" ++ c_name),
            clauses := replace_term_in_list clauses x new_const_term,
            conj := folform.replace_term conj x new_const_term,
            ds := replace_term_in_formlist ds x new_const_term in
        check_for_replacement xs ds clauses conj tt
      else
        check_for_replacement xs ds clauses conj bf
| [] ds clauses conj bf := (bf, ds, clauses, conj)

meta def check_const_terms : list folform → list axioma → folform → (list axioma × folform)
| (x :: xs) clauses conj :=
      -- tactic.trace x,
      -- TODO: the list of folforms stay constant no matter if we change clauses/conj
      --       Thus, we need to implement the functions above next to for the axiom list as well for a folform list and apply on xs
      --       Note, that we have to repeat the simplification with x as soon as we found something to simplify!
      let d := folform.get_all_const_terms x,
          (b, new_xs, clauses, conj) := check_for_replacement d (x::xs) clauses conj ff in
      if b
      then
        check_const_terms new_xs clauses conj
      else
        check_const_terms xs clauses conj
| [] clauses conj := (clauses, conj)

meta def axiomas_to_folforms : list axioma → list folform
| (x :: xs) := [x.f] ++ axiomas_to_folforms xs
| [] := []

meta def simplify_terms (clauses: list axioma) (conj: folform) : (list axioma × folform) :=
    -- In general: Check for terms that only occur in their constant form
    -- Example: term abc('test', 'c') where abc is not used anywhere else in combination with variables (neither abc('test',V), abc(V,'c') nor abc(V1,V2)), we can simplify it to a new constant 'abc_test_c')
    -- This procedure can be structured into three steps:
    -- 1) Identify all possible constant terms
    -- 2) Check if those terms only occur in that form in the corpus
    -- 3) If step 2 was successful, perform simplification
    let formula := (axiomas_to_folforms clauses) ++ [conj] in
    check_const_terms formula clauses conj