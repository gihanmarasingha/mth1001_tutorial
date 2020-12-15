import tactic
import data.set
import logic.basic

open set

namespace mth1001

section intersection_and_union

-- We'll deal with sets on a type `U`.
variable U : Type*
variables A B C : set U

/-
Typing set notation in Lean:

`∪` is `\cup`
`∩` is `\cap`
`∈` is `\in`
`∉` is `\notin`
`∅` is `\empty`
-/


/-
Throughout this file, we use `mem_inter_iff` and `mem_union_eq` to rewrite intersections and
unions as conjunctions and disjunctions.
-/
example (x : U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by rw mem_inter_iff
example (x : U) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by rw mem_union_eq

/-
We prove right distributivity of intersection over union.
-/
example : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) :=
begin
  ext, -- Assume `x : U`. It suffices to show `x ∈ (A ∪ B) ∩ C ↔ x ∈ (A ∩ C) ∪ (B ∩ C)`.
  -- Repeatedly apply the basic theorems on membership of intersections and unions.
  -- `or_and_distrib_right` is the distributive law, `(P ∨ Q) ∧ R ↔ (P ∧ Q) ∨ (Q ∧ R)`.
  calc x ∈ (A ∪ B) ∩ C
        ↔ x ∈ (A ∪ B) ∧ x ∈ C                : by rw mem_inter_iff
    ... ↔ (x ∈ A ∨ x ∈ B) ∧ x ∈ C            : by rw mem_union_eq
    ... ↔ (x ∈ A ∧ x ∈ C) ∨ (x ∈ B ∧ x ∈ C)  : by rw or_and_distrib_right
    ... ↔ x ∈ A ∩ C ∨ x ∈ B ∩ C              : by rw [mem_inter_iff, mem_inter_iff]
    ... ↔ x ∈ (A ∩ C) ∪ (B ∩ C)              : by rw mem_union_eq,            
end

-- Alternatively, we can just rewrite the goal many times.
example : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) :=
begin
  ext, -- Assume `x : U`. It suffices to show `x ∈ (A ∪ B) ∩ C ↔ x ∈ (A ∩ C) ∪ (B ∩ C)`.
  repeat { rw mem_inter_iff }, 
  repeat { rw mem_union_eq, },
  repeat { rw mem_inter_iff },
  rw or_and_distrib_right,  
end

/-  ***************************
    Laws of propositional logic
    *************************** -/

-- Feel free to use the following laws in the proofs below.

variables p q r : Prop

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by rw or_and_distrib_left
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by rw and_or_distrib_left
example : (p ∨ q) ∧ r ↔ (p ∧ r) ∨ (q ∧ r) := by rw or_and_distrib_right
example : (p ∧ q) ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by rw and_or_distrib_right
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)       := by rw and_assoc
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)       := by rw or_assoc
example : p ∨ false ↔ p                   := by rw or_false
example : p ∧ false ↔ false               := by rw and_false
example : p ∧ p ↔ p                       := by rw and_self
example : p ∨ p ↔ p                       := by rw or_self

-- Exercise 131:
-- Adapt either of the proofs above to give the following distributive law.
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  sorry  
end

-- Exercise 132:
example : A ∩ B = B ∩ A :=
begin
  sorry  end

-- Exercise 133:
example : A ∪ B = B ∪ A :=
begin
  sorry  
end

-- Exercise 134:
example : (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
begin
  sorry  
end

-- Exercise 135:
example : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
begin
  sorry  
end

-- Exercise 136:
example : A ∩ A = A :=
begin
  sorry  
end

/-
For the next result, we use `empty_def` and `mem_set_of_eq`, statements that are equivalent to our
mathematical definitions of empty set and set membership, respectively.
-/
example : ∅ = {x : U | false}                            := by rw empty_def
example (P : U → Prop) (z : U) : z ∈ {x : U | P x} = P z := by rw mem_set_of_eq

example : A ∩ ∅ = ∅ :=
begin
  ext x, -- Assume `x : U`. It remains to prove `x ∈ A ∩ ∅ ↔ x ∈ ∅`.
  rw mem_inter_iff, -- Rewrite `x ∈ A ∩ ∅` as `x ∈ A ∧ x ∈ ∅`.
  rw empty_def, -- Rewrite `∅` as `{x : U | ⊥}`.
  rw mem_set_of_eq, -- Rewrite `x ∈ {x : U | ⊥}` as `⊥`.
  rw and_false, -- Complete the goal using the result `P ∧ ⊥ ↔ ⊥` and reflexivity of `↔`.
end

-- Exercise 137:
example : A ∪ ∅ = A :=
begin
  sorry  
end

end intersection_and_union

end mth1001
