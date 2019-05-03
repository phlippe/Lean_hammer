import .datastructures_hol

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

meta def add_axiom (n : name) (axioma : holform) : hammer_tactic unit :=
do state_t.modify (fun state, {state with axiomas := ⟨n, axioma⟩ :: state.axiomas})

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


meta mutual def hammer_c, hammer_g, hammer_f
with hammer_c : expr → hammer_tactic holterm
| e@(expr.const n _) := 
  do 
    -- TODO deviation from specification, map constants : sth : Prop to prf
    -- is this necessary?
    -- tactic.trace e,
    t ← tactic.infer_type e, -- consult the environment (get type of expression)
    lip ← lives_in_prop_p t, -- check whether t is prop or not
    if lip
    then
      return $ holterm.prf -- What about the type/formula it actually proofs?
    else
      return $ holterm.const $ (remove_suffix_of_string n.to_string.to_list).as_string 
| (expr.local_const n pp _ t) := -- Same for local constants
  do  tactic.trace ("Found local constant"),
      lip ← lives_in_prop_p t,
      if lip
      then
        return $ holterm.prf
      else
        do  ttype ← (hammer_g t),
            return $ holterm.lconst n ttype
| (expr.app t s) := -- Application (in paper C_Γ(ts)=...)
  do  tp ← hammer_c t, -- Get C_Γ(t)
      sp ← hammer_c s, -- Get C_Γ(s)
      match tp with
      | holterm.prf := return holterm.prf -- If C_Γ(t) is type proof, then just return type proof
      | _ := -- Anything else: check what type C_Γ(s) has
        match sp with
        | holterm.prf := return tp -- If it is a proof, return C_Γ(t)
        | _ := return $ holterm.app tp sp -- else: Return C_Γ(t) applied on C_Γ(s)
        end
      end

| e@(expr.pi n n1 t _) := -- Dependent types (in paper C_Γ(Πx:t.s) )
  do  lip ← lives_in_prop_p e,
      Fn ← mk_fresh_name,
      let F := holterm.const Fn, -- Fresh constant F
      let An := n ++ Fn, -- Axiom name
      ys ← hammer_ff $ hammer_fc e, -- y = FF_Γ(FC(Γ;Πx:t.s))
      let ce0 := list.foldl (λ t (np : name × holtype), holterm.app t (holterm.lconst np.1 np.2)) F ys, -- Fy (for all elements in ys, apply F on them by creating local constant of the name)
      if lip 
      then -- If s is of type Prop: new axiom ∀y.P(Fy) ↔ F_Γ(Πx:t.s)  
        (do let ce1 := holform.P ce0, 
            ce2 ← hammer_f e, -- F_Γ(Πx:t.s)   
            add_axiom An $ wrap_quantifier holform.all ys (holform.iff ce1 ce2)) -- Add new axiom to tactic
      else 
        (do add_axiom An $ holform.top),
    -- TODO: Is this type checking necessary for HOL? We have probably encoded it in the type axioms before
    --   else -- Otherwise: new axiom ∀yz.T(z,Fy) ↔ G_Γ(z,Πx:t.s)  
    --     (do zn ← mk_fresh_name, -- Get new, fresh constant name
    --         tce0 <- holtype.infer_type ce0,
    --         let zlc := holterm.lconst zn tce0, -- Create local constant from this name
    --         let ys := (⟨zn, tce0⟩ :: ys : list $ name × holtype), -- Add this constant to the already existing set of free variables of our formula
    --         -- TODO: Understand this axiom and try to find the best translation to TF0
    --         let ce1 := holform.T zlc ce0, -- type checker T(z,Fy)
    --         ce2 ← hammer_g zlc e, -- type guard G_Γ(z,Πx:t.s) 
    --         add_axiom An $ wrap_quantifier holform.all ys (holform.iff ce1 ce2)), -- Add new axiom to tactic
      return ce0 -- Return Fy (what for is this necessary?)
| e@(expr.lam n _ _ _) := -- Lambda expression C_Γ(λx:τ.t)=Fy_0
  do  tactic.trace "Lambda",
      (t, xτs) ← collect_lambdas e, -- Get all lambda expressions in e
      α ← tactic.infer_type t, -- Infer the type of t given all lambda expression (Γ,x:τ|-t:α)
      tactic.trace α,
      tactic.trace t,
      tactic.trace e,
      let yρs := hammer_fc e, -- y: ρ = FC(Γ;λx:τ.t) - Get list of free constants in e
      Fn ← mk_fresh_name, -- Fresh constant name
      let An := n ++ Fn, -- ??? Add new constant name to list of current constants(?)
      y₀s ← hammer_ff yρs, -- 
      x₀s ← hammer_ff xτs, -- 
      let Ft :=
        list.foldr
          (λ (nt : name × holtype × expr) a,
            expr.pi nt.2.1.to_name binder_info.default nt.2.2 $ expr.abstract_local a nt.1)
          α
          $ yρs ++ xτs,
      -- instead of extending the environment, we use a local constant and keep track of its name
      add_constant Fn Ft,
      let F := @expr.local_const tt Fn Fn binder_info.default Ft,
      let (ce1a : expr) :=
        list.foldl 
          (λ (a : expr) (nt : name × holtype × expr), (a (expr.local_const nt.1 nt.2.1.to_name binder_info.default nt.2.2)))
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
      add_axiom An $ wrap_quantifier holform.all (y₀s ++ x₀s) ce1,
      return $
        list.foldl
          (λ a (nt : name × holtype), holterm.app a $ holterm.lconst nt.1 nt.2)
          (holterm.const Fn)
          y₀s
| e@(expr.elet x τ t s) := do tactic.trace "Found elet during translation",
                           undefined
-- TODO: Check if those need to be implemented as well
| e@(expr.var n) := do tactic.trace "Found variable during translation", 
                    return $ holterm.var n 
-- NEED TO BE IMPLEMENTED
| e@(expr.sort _) := do tactic.trace "Found sort during translation", 
                     undefined
                     -- hammer_c `(5)
| e@(expr.mvar _ _ _) := do tactic.trace "Found mvar during translation",  
                         undefined
| e@(expr.macro _ _) := do tactic.trace "Found macro during translation", 
                        undefined

with hammer_g : expr → hammer_tactic holtype
| e := return holtype.o
with hammer_f : expr → hammer_tactic holform
| e := return holform.bottom


run_cmd do (c, _) <- using_hammer $ hammer_c `(λ (x:ℕ), x + 1=5), tactic.trace $ holterm.repr c