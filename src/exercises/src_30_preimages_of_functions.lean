import data.set
import .src_17_even_odd_further

open set function

namespace mth1001

section pre_image
/-
Suppose `f : α → β` is a function from a type `α` to a type `β`. Suppose
`B` is a set on `β`. The *preimage* of `B` under `f` is `{x : α | f x ∈ B}`.
It is denoted `f⁻¹ B` in matheamtics and either `preimage f B` or `f⁻¹' B` in Lean.

WARNING: `f⁻¹ B` is a *set*. It is related to, but is not the same thing as the inverse of `f`.
-/

section pre_image_examples
/-
As an example, consider `g : ℤ → ℕ` given by `g n := |n| + 1`. Let `T := {1, 3, 5}`. Then the
preimage of `T` under `g` is the set `{0, 2, -2, 4, -4}`.
-/

def g (n : ℤ) : ℕ := int.nat_abs n + 1
def T : set ℕ := {1, 3, 5}

lemma eq_or_eq_neg_of_nat_abs_eq {x : ℤ} {y : ℕ}: int.nat_abs x = y → (x = y) ∨ (x = -y) := 
λ h, h ▸ (h ▸ (int.nat_abs_eq x))

example : g⁻¹' T = {0, 2, -2, 4, -4} :=
begin
  ext, unfold T,
  split,
  { unfold preimage,
    intro h,
    rw mem_set_of_eq at h,
    unfold g at h,
    rcases h with h | h | h | ⟨⟨⟩⟩,
    { rcases (eq_or_eq_neg_of_nat_abs_eq (nat.succ_inj h)) with rfl | rfl;
      simp, },
    { rcases (eq_or_eq_neg_of_nat_abs_eq (nat.succ_inj h)) with rfl | rfl;
      simp, },
    { rw (int.eq_zero_of_nat_abs_eq_zero (nat.succ_inj h)), simp, }, },
  { intro h,
    finish, },
end

/-
As an example, conisder `f : ℤ → ℤ` defined by `f n = n + 1`. Let `B` be the set of even integers.
We'll show the preimage of `B` under `f` is the set of odd integers
-/

def f (n : ℤ) : ℤ := n + 1
def B := {y : ℤ | even y}
def C := {m : ℤ | odd m}

example : f⁻¹' B = C :=
begin
  ext, -- Assume `x ∈ ℤ`. We must show `x ∈ f⁻¹' B ↔ x ∈ C`.
  split,
  { rintro ⟨b, h⟩, -- Assume `b : ℤ` and `h : f x = 2 * b`. We must show `x ∈ C`.
    unfold f at h, -- By defintion, `h : f x = 2 * b`.
    use (b - 1), -- It suffices to prove `x = 2 * b + 1`.
    linarith, }, -- The goal follows by linear arithmetic.
  { rintro ⟨c, h⟩, -- Assume `c : ℤ` and `h : x = 2 * c + `. We must show `x ∈ f⁻¹' B`.
    have h₂ : f x ∈ B,
    { rw h,
      unfold f,
      use (c + 1),
      linarith, },
    unfold preimage,
    rw mem_set_of_eq,
    exact h₂, },
end

end pre_image_examples

section pre_image_theorems

variable {α : Type*}
variable {β : Type*}

#check preimage_inter

/-
The following proof uses the power of `rintro` to decompose intersections, etc.
Note that, unlike images, intersections are preserved by the preimage.
-/
theorem preimage_inter {B C : set β} {f : α → β} : f⁻¹' (B ∩ C) = f⁻¹' B ∩ f⁻¹' C :=
begin
  ext, -- Assume `x : ℤ`. It suffices to prove `x ∈ f⁻¹' (B ∩ C) ↔ x ∈ f⁻¹' B ∩ f⁻¹' C`.
  split, -- Decompose the `↔` proof into two implication proofs.
  { rintro ⟨hb, hc⟩, -- Assume `hb : f x ∈ B` and `hc : f x ∈ B`. STP `x ∈ f⁻¹' B ∩ f⁻¹' C`.
    exact and.intro hb hc, }, -- This follows by `∧` introduction on `hb` and `hc`.
  { rintro ⟨hb, hc⟩, -- Assume `hb : x ∈ f⁻¹' B` and `hc : x ∈ f⁻¹' C`. STP `x ∈ f⁻¹' B ∩ C`.
    exact and.intro hb hc, } -- The goal follows by `∧` introduction on `hb` and `hc`.
end

/-
In fact, as the same tactic applies to both subgoals after the split above, the proof can be
shortened using the `;` combinator:
-/
example {B C : set β} {f : α → β} : f⁻¹' (B ∩ C) = f⁻¹' B ∩ f⁻¹' C :=
begin
  ext, -- Assume `x : ℤ`. It suffices to prove `x ∈ f⁻¹' (B ∩ C) ↔ x ∈ f⁻¹' B ∩ f⁻¹' C`.
  split; -- Decompose the `↔` proof into two implication proofs.
  { rintro ⟨hb, hc⟩, exact and.intro hb hc, },
end

-- Exercise 144:
-- The preimage of a union is the union of preimages.
theorem preimage_union {B C : set β} {f : α → β} : f⁻¹' (B ∪ C) = f⁻¹' B ∪ f⁻¹' C :=
begin
  sorry  
end

end pre_image_theorems

end pre_image

end mth1001
