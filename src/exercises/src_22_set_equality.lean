import data.set
import data.finset
import logic.basic

namespace mth1001

open set

namespace set_membership

-- We use `finset ℕ` to denote the type of finite sets of elements of `ℕ`.

def A := ({1, 2, 3, 4} : finset ℕ) -- This defines `A` to be `{1, 2, 3, 4}`.
def B := ({1, 3, 5, 6} : finset ℕ)
def C := ({5, 7, 9} : finset ℕ)

/-
Type `∈` as `\in`,
type `∉` as `\notin`,
type `∩` as `\cap`, 
type `∪` as `\cup`,
type `⊆` as `\sub`,
type `∅` as `\empty`
type `\` as `\`,
type `ℕ` as `\N` and `ℤ` as `\Z`.
-/

/-
`dec_trivial` proves results by 'decidability'. You don't need to know what this means.
Lean can use `dec_trivial` to prove results for particular finite sets.
-/ 

example : 2 ∈ A := dec_trivial

example : 5 ∉ A := dec_trivial

example : 3 ∈ (A ∩ B) := dec_trivial

end set_membership

section set_equality

/-
Whenever an mathematical object is defined by its external properties, the Lean tactic `ext`
transforms a proof of equality of two objects into a proof of checking that they have the same
external properties. This corresponds to the mathematical principle of *extensionality*.

In the case of proving two sets `S` and `T` on a type `A` are equal, the `ext` tactic transforms
`⊢ S = T` into an assumption `x : A` and a new goal `⊢ x ∈ S ↔ x ∈ T`.
-/

-- We'll look at sets over a type A.

variable A : Type*

theorem set_refl : ∀ S : set A, S = S :=
begin
  intro S, -- Assume S is a set.
  ext, -- Assume `x : A`. It suffices to prove `x ∈ S ↔ x ∈ S`.
  refl, -- The result follows by reflexivity of `↔`.
end

theorem set_symm : ∀ S T : set A, S = T → T = S:=
begin
  intros S T, -- Assume S and T are sets.
  intro h, -- Assume `h : ∀ x, x ∈ S ↔ x ∈ T`. It suffices to prove `∀ x, x ∈ T ↔ x ∈ S`.
  ext,       -- Assume `x : A`. It suffices to prove `x ∈ T ↔ x ∈ S`.
  symmetry, -- By symmetry of `↔`, it suffices to prove `x ∈ S ↔ x ∈ T`.
  rw h, -- This follows from `h`.
end

-- Exercise 127:
-- In this exercise, it will be helpful to use the `iff.trans` function. If
-- `h₁ : p ↔ q` and `h₂ : q ↔ r`, then `iff.trans h₁ h₂` is a proof of `p ↔ r`.
theorem set_trans : ∀ S T U : set A, (S = T) ∧ (T = U) → S = U :=
begin
  intros S T U, -- Assume S, T, and U are sets.
  intro h, -- Assume `h : S = T ∧ T = U`.
  ext, -- Assume `x : A`. It suffices to prove `x ∈ S ↔ x ∈ U`.
  have h₂ : x ∈ S ↔ x ∈ T, sorry, 
  have h₃ : x ∈ T ↔ x ∈ U, sorry, 
  sorry  
end

end set_equality

section finite_set_equality

/-
In the next example, we show `{5, 6, 7, 8} = {5, 7, 5, 8, 6}`. Note that we must explicitly
specify the type of the set. For example, `({5, 6, 7, 8 } : set ℤ)` is the Lean way to
write `{5, 6, 7, 8}`.
-/

example : ({5, 6, 7, 8} : finset ℤ) = ({5, 7, 5, 8, 6} : finset ℤ) := dec_trivial

-- Likewise, we can prove two particular finite sets are not equal by `dec_trivial`.

example : ({5, 6, 7, 8} : finset ℤ) ≠ ({5, 5, 8, 6} : finset ℤ) := dec_trivial


/-
The proofs are a bit challenging if we don't use `dec_trivial`. The `finish` tactic proves goals
by applying rules of logic.
-/

example : ({5, 6, 7, 8} : set ℤ) = ({5, 7, 5, 8, 6} : set ℤ) :=
begin
  ext,        -- Use set extensionality.
  finish,     -- Finish using rules of logic.
end

/-
To prove set inequalities, we can use the `finish` tactic, but we also need to identify an element
that belongs to one set but not to the other. We also the set-specific function extenstionality
result `ext_iff`.
-/

example : ({5, 6, 7, 8} : set ℤ) ≠ ({5, 5, 8, 6} : set ℤ) :=
begin
  intro h, -- Assume `h : {5, 6, 7, 8} = {5, 5, 8, 6}`.-- It suffices to prove `⊥`
  rw ext_iff at h, -- By definition, `h : ∀ x, x ∈ {5, 6, 7, 8} ↔ x ∈ {5, 5, 8, 6}`.
  contrapose! h,   -- Negating this, the goal is `∃ x, ¬(x ∈ {5, 6, 7, 8} ↔ x ∈ {5, 5, 8, 6})`.
  use 7, -- By `∃` intro. on `7`, it suffices to prove `¬(7 ∈ {5, 6, 7, 8} ↔ 7 ∈ {5, 5, 8, 6})`.
  finish, -- Finish using rules of logic.
end

end finite_set_equality


end mth1001

