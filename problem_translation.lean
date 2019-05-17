import .tptp.tptp 
import .tptp.translation_tptp
import .tptp.simplification_tptp
-- import .tff.tff
-- import .tff.translation_tff
-- import .tff.simplification_tff

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
              do  lis <- lives_in_type r, -- TODO: Implement check of τ for Set and Type!
                if lis
                then 
                  do  xn ← mk_fresh_name,
                      let f := folterm.lconst xn xn,
                      -- let f := folterm.lconst xn (foltype.from_name xn),
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

meta def expr_in_parts : expr → tactic expr 
| e@(expr.lam n b a c) := do tactic.trace ("Lambda expression with var " ++ name.to_string n ++ " and type "), tactic.trace a, new_c <- (expr_in_parts c), return $ e
| e@(expr.pi n b a c) := do tactic.trace ("Pi expression with var " ++ name.to_string n ++ " and type "), tactic.trace a, new_c <- (expr_in_parts c), return $ e
| e@(expr.const n _) := do tactic.trace ("Constant with name " ++ name.to_string n), return $ e
| e@(expr.app t1 t2) := do tactic.trace ("Application"), new_t1 <- expr_in_parts t1, new_t2 <- expr_in_parts t2, return $ e
| e@(expr.local_const n n1 _ _) := do tactic.trace ("Local constant with name " ++ name.to_string n ++ " and second name " ++ name.to_string n1), return $ e
| e@(expr.elet x τ t s) := do tactic.trace ("Let expression"), return e
| e@(expr.var n) := do tactic.trace ("Variable "), tactic.trace n, return $ e
| e := do tactic.trace ("Unknown expression"), tactic.trace e, return e


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

meta def problem_to_tptp_format (declr: list name) (clauses: list expr) (conjecture: expr) : hammer_tactic format := 
  do  
    ⟨cl,cl_state⟩ <- using_hammer (translate_problem declr clauses),
    ⟨conj,conj_state⟩ <- using_hammer (hammer_f conjecture),
    ⟨cl_list,conj⟩ <- simplify_terms (hammer_state.axiomas cl_state) conj,
    -- let cl_list := (hammer_state.axiomas cl_state), -- For debugging, if no simplification should be applied
    return $ export_formula cl_list conj

-- meta def problem_to_tff_format (declr: list name) (clauses: list expr) (conjecture: expr) : hammer_tactic format := 
--   do  
--     ⟨cl,cl_state⟩ <- using_hammer (translate_problem declr clauses),
--     ⟨conj,conj_state⟩ <- using_hammer (hammer_f conjecture),
--     ⟨td_list,cl_list,conj⟩ <- simplify_terms (hammer_state.type_definitions cl_state) (hammer_state.axiomas cl_state) conj,
--     -- ⟨cl_list,conj⟩ <- simplify_terms cl_list conj, -- TODO: Fix problem of not getting all simplifications in the first run (see function comments)
--     return $ export_formula td_list cl_list conj