--#######################
--## Premise selection ##
--#######################
-- Relies on old cold from Rob: https://github.com/robertylewis/relevance_filter/tree/dev_lean_reparam
import meta.rb_map data.list.basic data.nat.sqrt

open tactic
open native

meta def collect_consts (e : expr) : name_set :=
e.fold mk_name_set
  (λ e' _ l, match e' with
  | expr.const nm _ := l.insert nm
  | _ := l
  end)

meta def name_set.inter (s1 s2 : name_set) : name_set :=
  s1.fold mk_name_set (λ nm s, if s2.contains nm then s.insert nm else s)


#check rb_map.ifind
-- this is in mathlib
/- meta def rb_map.ifind {α β} [inhabited β] (map : rb_map α β) (a : α) : β :=
match map.find a with
| some b := b
| none := default β
end -/

meta def rb_set.of_list {α : Type} [has_lt α] [decidable_rel ((<) : α  → α → Prop)] : list α → rb_set α
| [] := mk_rb_set
| (h::t) := (rb_set.of_list t).insert h

meta def find_nameset (map : rb_map name name_set) (feature : name) : name_set := ((map.find feature).get_or_else mk_name_set)

-- meta def rb_set.inth {α} [inhabited α] (s : rb_set α) (i : ℕ) : α :=
-- s.keys.inth i

/--
 map sends a name to the set of names which reference it.
 update_features_map extends this map by adding idx to the set for each name in refs.
-/
meta def update_features_map (map : rb_map name name_set) (idx : name) (refs : name_set) : rb_map name name_set :=
refs.fold map (λ nm map', map'.insert nm (((map'.find nm).get_or_else mk_name_set).insert idx))

/--
 Given a new declaration and the current collected data, adds the info from the new declaration.
 Returns (contents_map, features_map, names), where
  - contents_map maps a name dcl to a pair of name_sets (tp_consts, val_consts), where tp_consts contains
     the symbols appearing in the type of dcl and val_consts contains the symbols appearing in the type of dcl
  - features_map maps a name nm to the set of names for which nm appears in the value
  - names is a list of all declaration names that have appeared
-/

meta def update_name_maps (dcl_name : name) (dcl_type : expr) (dcl_value : expr) :
     (rb_map name (name_set × name_set) × (rb_map name name_set) × Σ n, array n name) →
         (rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array n name
| (contents_map, features_map, ⟨n, names⟩):=
  let val_consts := collect_consts dcl_value,
      tp_consts := collect_consts dcl_type,
      contents_map' := contents_map.insert dcl_name (tp_consts, val_consts),
      features_map' := update_features_map features_map dcl_name tp_consts in
  (contents_map', features_map', ⟨_, names.push_back dcl_name⟩)

/--
 Maps update_name_maps over the whole environment, excluding meta definitions.
 Returns (contents_map, features_map, names), where
  - contents_map maps a name dcl to a pair of name_sets (tp_consts, val_consts), where tp_consts contains
     the symbols appearing in the type of dcl and val_consts contains the symbols appearing in the value of dcl
  - features_map maps a name nm to the set of names for which nm appears in the value
  - names is a list of all declaration names that have appeared
-/
meta def get_all_decls : tactic ((rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array n name) :=
do env ← get_env,
   return $ env.fold
    (mk_rb_map, mk_rb_map, ⟨0, array.nil⟩)
    (λ dcl nat_arr,
     match dcl with
     | declaration.defn nm _ tp val _ tt := update_name_maps nm tp val nat_arr
     | declaration.thm nm _ tp val := update_name_maps nm tp val.get nat_arr
     | _ := nat_arr
     end)

section features_map
variable features_map : rb_map name name_set

-- this is in mathlib and is more efficient
#check nat.sqrt
/- def sqrt_aux : ℕ → ℕ → ℕ
| 0 n := 0
| (nat.succ s) n := if (nat.succ s)*(nat.succ s) ≤ n then nat.succ s else sqrt_aux s n

def sqrt (n : ℕ) : ℕ := sqrt_aux n n -/

-- it's possible this exists in mathlib already
meta def log_aux : ℕ → ℕ → ℕ → ℕ
| 0 base n := if 1 ≤ n then log_aux 1 base n else 0
| (nat.succ c) base n := if (nat.pow base (nat.succ c)) ≤ n then log_aux (nat.succ $ nat.succ c) base n else c

meta def log (n : ℕ) (base : ℕ) : ℕ := log_aux 0 base n

#check list.sum
/- meta def sum_list : list ℕ → ℕ
| (x::xs) := x + sum_list xs
| [] := 0 -/

meta def feature_weight (feature : name) : ℕ :=
let l := (find_nameset features_map feature).size in
if l > 0 then log l 10 else 0

meta def feature_distance (f1 f2 : name_set) : ℕ :=
let common := f1.inter f2 in
(common.to_list.map (λ n, nat.pow (feature_weight features_map n) 6)).sum

meta def name_distance (contents_map : rb_map name (name_set×name_set)) (n1 n2 : name) : ℕ :=
let f1 := ((contents_map.find n1).get_or_else (mk_name_set, mk_name_set)).1,
    f2 := ((contents_map.find n2).get_or_else (mk_name_set, mk_name_set)).1 in
feature_distance features_map f1 f2

meta def name_feature_distance (contents_map : rb_map name (name_set×name_set)) (n1 : name) (f2 : name_set) : ℕ :=
let f1 := ((contents_map.find n1).get_or_else (mk_name_set, mk_name_set)).1 in
feature_distance features_map f1 f2

end features_map

/-
Sorting on arrays.
-/

section quicksort

variables {α : Type}  [inhabited α]
  (op : α → α → bool)
local infix `<` := op
variable  [has_to_format α]

meta def swap {n : ℕ} (A : array n α) (i j : ℕ) : array n α :=
let tmp_j := A.read' j,
    tmp_i := A.read' i in
(A.write' j tmp_i).write' i tmp_j

meta def partition_aux (hi : ℕ) (pivot : α) {n : ℕ} : Π (A : array n α) (i j : ℕ), ℕ × array n α
| A i j :=
if j = hi then (i, A) else
let tmp_j := A.read' j in
if bnot (tmp_j < pivot) then partition_aux A i (j+1) else
  let tmp_i := A.read' i,
      A' := (A.write' j tmp_i).write' i tmp_j in
  partition_aux A' (i+1) (j+1)
--else
--  partition_aux A i (j+1)

meta def partition {n : ℕ} (A : array n α) (lo hi : ℕ) : ℕ × array n α :=
let pivot := A.read' hi,
    i := lo,
    (i', A') := partition_aux op hi pivot A i lo,
    A'' := if A'.read' hi < A'.read' i' then swap A' i' hi else A' in
(i', A'')

meta def quicksort_aux {n : ℕ} : Π (A : array n α) (lo hi : ℕ), array n α
| A lo hi :=
if bnot (nat.lt lo hi) then A else
let (p, A') := partition op A lo hi in
quicksort_aux (quicksort_aux A' lo (p-1)) (p+1) hi


meta def quicksort {n : ℕ} (A : array n α) : array n α :=
quicksort_aux op A 0 (n-1)

meta def partial_quicksort_aux {n : ℕ} : Π (A : array n α) (lo hi k : ℕ), array n α
| A lo hi k :=
if nat.lt lo hi then
  let (p, A') := partition op A lo hi,
      A'' := partial_quicksort_aux A' lo (p-1) k in
  if nat.lt p (k-1) then partial_quicksort_aux A'' (p+1) hi k else A''
else A

meta def partial_quicksort {n : ℕ} (A : array n α) (k : ℕ) : array n α :=
partial_quicksort_aux op A 0 (n-1) k

end quicksort

meta def find_smallest_in_array {n α} [inhabited α] (a : array n α) (lt : α → α → bool) : list α :=
a.foldl [] (λ nm l, if lt nm (l.head) then [nm] else if lt l.head nm then l else nm::l)

meta def nearest_k (features : name_set) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × nat) :=
let arr_val_pr : array n (name × nat) := ⟨λ i, let v := names.read i in (v, name_feature_distance features_map contents_map v features)⟩,
    sorted := partial_quicksort
      (λ n1 n2 : name × nat, nat.lt n2.2 n1.2)
       arr_val_pr k,
    name_list := if h : k ≤ n then (sorted.take k h).to_list else sorted.to_list in
name_list

meta def nearest_k_of_expr (e : expr) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × nat) :=
let features := collect_consts e in nearest_k features contents_map features_map names k

meta def nearest_k_of_name (nm : name) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × nat) :=
let features := ((contents_map.find nm).get_or_else (mk_name_set, mk_name_set)).1 in nearest_k features contents_map features_map names k

def find_val_in_list {α β} [decidable_eq α] [inhabited β] (a : α) : list (α × β) → β
| [] := default β
| ((a', b)::t) := if a = a' then b else find_val_in_list t

meta def relevance_to_feature (goal : name_set) (feature : name) (contents_map : rb_map name (name_set × name_set))
     (nearest : list (name × nat)) : nat :=
let --nearest_map := rb_map.of_list nearest,
    contains_feature := nearest.filter (λ b : name × nat, ((contents_map.find b.1).get_or_else (mk_name_set, mk_name_set)).2.contains feature),
    weighted_vals := (contains_feature.map
     (λ nm_flt : name × nat, nm_flt.2 / ((contents_map.find nm_flt.1).get_or_else (mk_name_set, mk_name_set)).2.size)) in
((27 : nat) / 10)* weighted_vals.sum + find_val_in_list feature nearest  --nearest_map.ifind feature


-- TODO: the k in nearest_k shouldn't be the same as the argument k
meta def find_k_most_relevant_facts_to_goal (goal : name_set)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × nat) :=
let nearest := nearest_k goal contents_map features_map names k,
    name_val_prs : array n (name × nat) := ⟨λ i, let v := names.read i in (v, relevance_to_feature goal v contents_map nearest)⟩,
    relevant := partial_quicksort (λ n1 n2 : name × nat, nat.lt n2.2 n1.2) name_val_prs k,
    name_list := if h : k ≤ n then (relevant.take k h).to_list else relevant.to_list in
name_list


meta def find_k_most_relevant_facts_to_expr (goal : expr)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × nat) :=
let features := collect_consts goal in
find_k_most_relevant_facts_to_goal features contents_map features_map names k

run_cmd do let nm := collect_consts `(1+1=2), tactic.trace $ name_set.to_list nm

/-
The VM representation of an array allows for destructive updates if the reference count is 1.
You can see this behavior with a trace option. If you do any big array computations, you should
try your hardest to keep all reference counts ≤ 1 to allow this. Otherwise this will get very slow.
@[reducible] and @[inline] attributes can help with this.
-/
set_option trace.array.update true
#eval array.to_list $ quicksort (λ x y, x ≤ y) $ list.to_array [3, 5, 1003, 1, 1, 99, 5]

