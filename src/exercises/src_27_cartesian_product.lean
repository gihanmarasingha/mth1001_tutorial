import data.set
import logic.basic

open set 

namespace mth1001

section cartesian_product
-- In this file, we'll deal with two types, `U` and `V`.
variables (U : Type*) (V : Type*)
variables (S T : set U) (A B : set V)


/-
`U × V` is the (Cartesian) product type of `U` and `V`. It is the type of all pairs `(u,v)`, where
`u : U` and `v : V`.
-/
#check U × V

/-
WARNING: In Lean, the `×` symbol denotes the Cartesian product of types, not sets. However, we
can use the following special command to make Lean temporarily treat `×` as a set product.
-/
local notation a `×` b := set.prod a b

-- In addition to the results `mem_inter_iff`, `mem_union_eq`, `mem_diff` introduced in
-- the previous files, we'll use `mem_prod` to rewrite a product of two sets.

example (x : prod U V) : x ∈ (S × A) ↔ x.fst ∈ S ∧ x.snd ∈ A := by rw mem_prod

example : (S × (A ∪ B)) = (S × A) ∪ (S × B) :=
begin
  ext, -- Assume `x : U × V`. It suffices to prove `x ∈ (S × (A ∪ B)) ↔ x ∈ (S × A) ∪ (S × B)`.
  rw [mem_prod, mem_union_eq, mem_union_eq, mem_prod, mem_prod],
  rw and_or_distrib_left, -- Complete using left distributivity of `∧` over `∨`.
end

-- Exercise 139:
-- In this example, feel free to use the `tauto` tactic to finish the 'logic' part of the proof.
example : (S × (A ∩ B)) = (S × A) ∩  (S × B) :=
begin
  sorry  
end

-- Exercise 140:
-- For this example, you'll either need De Morgan's law or the `tauto!` tactic which,
-- unlike `tauto`, is permitted to use classical reasoning.
example : (S × (A \ B)) = (S × A) \  (S × B) :=
begin
  sorry  
end


end cartesian_product

end mth1001
