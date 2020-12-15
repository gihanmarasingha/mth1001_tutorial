import data.set
import logic.basic

open set

namespace mth1001

section set_difference

variable U : Type* -- We'll have sets on the type `U`.
variables A B C : set U

-- In addition to `mem_inter_iff` and `mem_union_eq` from the previous file, we'll
-- now use `mem_diff` for the set difference

example (x : U) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := by rw mem_diff

-- We need the follow two lines to admit classical reasoning.
open classical
local attribute [instance] prop_decidable

-- In addition to the rules of propositional logic given in the previous file, we use
-- De Morgan's laws, as follows.

example (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by rw not_and_distrib
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by rw not_or_distrib

example : A \ (B ∩ C) = (A \ B) ∪ (A \ C) :=
begin
  ext, -- Assume `x : U`. It suffices to prove `x ∈ A \ (B ∩ C) ↔ x ∈  (A \ B) ∪ (A \ C)`. 
  -- Rewrite using definitions of set difference, intersection, and union.
  rw [mem_diff, mem_union_eq, mem_inter_iff, mem_diff, mem_diff],
  rw not_and_distrib,        -- De Morgan's law
  rw and_or_distrib_left,    -- Distributivity of conjunction over disjunction
end

-- Exercise 138:
-- In addition to De Morgan's law, the propositional logic aspect of the following problem requires
-- several applications of the laws featured in the previous file. If you get irritated, the
-- `tauto` tactic will close many goals in propositional logic.
example : A \ (B ∪ C) = (A \ B) ∩ (A \ C) :=
begin
  ext,
  rw [mem_diff, mem_union_eq, mem_inter_iff, mem_diff, mem_diff],
  rw not_or_distrib,        -- De Morgan's law
  rw and_comm (x ∈ A) (x ∉ B),
  sorry  
end 


end set_difference

end mth1001
