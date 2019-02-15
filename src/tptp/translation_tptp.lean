import .tptp 

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
