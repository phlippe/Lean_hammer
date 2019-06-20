import .datastructures_hol
import .translation_hol
import .boolean_free_HOL

--######################################
--## Translating declarations for HOL ##
--######################################

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
        do  lit <- lives_in_prop_p r, -- Check if τ=Prop (or rather t : Prop)
            if lit
            then -- If yes, add new axiom c ↔ F(t)
              do  (fe1,_) <- using_hammer (hammer_f l),
                  (fe2,_) <- using_hammer (hammer_f r),
                  Cn ← mk_fresh_name,
                  add_axiom Cn (holform.iff fe1 fe2)
            else -- Otherwise, check whether τ is from type Set or Type, or another type
              do  Cn <- mk_fresh_name,
                  (Cc,_) <- using_hammer (hammer_c r),
                  (Ct,_) <- using_hammer (hammer_c l),
                  add_axiom Cn (holform.eq Cc Ct)
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
              (Gcτ,_) <- using_hammer (hammer_g  τ),
              add_type_def Cn (remove_suffix_of_string c.to_string.to_list).as_string Gcτ

meta def process_declarations : list name → hammer_tactic unit
| [] := tactic.skip 
| (x :: xs) := 
    do 
      d ← tactic.get_decl x,
      translate_axiom_expression d.value,
      process_declarations xs


--###############################
--## Final problem translation ##
--###############################

meta def translate_declaration (e : name) : hammer_tactic unit :=
do 
    env <- tactic.get_env,
    d <- tactic.get_decl e,
    l ← tactic.get_eqn_lemmas_for tt e,
    process_declarations (l.append [e])

meta def translate_problem: list name → list expr → hammer_tactic unit
| [] [] := tactic.skip 
| [] (x::xs) := do translate_axiom_expression x, translate_problem [] xs
| (y::ys) xs := do translate_declaration y, translate_problem ys xs

meta def problem_to_hol_format (declr: list name) (clauses: list expr) (conjecture: expr) : hammer_tactic format := 
  do  
    ⟨cl,cl_state⟩ <- using_hammer (translate_problem declr clauses),
    ⟨conj,conj_state⟩ <- using_hammer (hammer_f conjecture),
    let cl_list := (hammer_state.axiomas cl_state), -- For debugging, if no simplification should be applied
    let td_list := (hammer_state.type_definitions cl_state), -- For debugging, if no simplification should be applied
    
    let conj := hol_formula_wo_bool conj,
    let cl_list := axiom_list_wo_bool cl_list,
    let td_list := typedef_list_wo_bool td_list,

    return $ export_formula td_list cl_list conj


run_cmd do ⟨f,_⟩ <- using_hammer $ problem_to_hol_format [`fib] 
                        [`(Π(x:ℕ), x + 1 = nat.succ x), `(nat.succ 0 = 1), `(nat.succ 1 = 2)]       -- , `(0:ℕ), `(1:ℕ), `(2:ℕ), `(3:ℕ), `(4:ℕ), `(5:ℕ), `(6:ℕ), `(7:ℕ), `(8:ℕ), `(Π x y : ℕ, sum_two x y =x+y)
                        `((fib 2 = 2)), 
           tactic.trace f 

-- TODO: Change $i to NAT (is individual, not integer)           