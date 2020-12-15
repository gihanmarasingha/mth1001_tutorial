import ..library.src_real_field
import ..library.src_ordered_field_lemmas
import data.set.basic
import tactic

namespace mth1001

namespace myreal

open myreal_field classical myordered_field

open_locale classical

variables {R : Type} [myreal_field R]

def has_upper_bound (S : set R) := ∃ u : R, upper_bound u S

lemma sup_is_sup {S : set R} (h₁ : has_upper_bound S) (h₂ : S ≠ ∅) : is_sup (sup S) S :=
begin
  have h₃ : ∃ x : R, is_sup x S, from completeness h₂ h₁,
  have h₄ : sup S = some h₃, from dif_pos h₃,
  rw h₄,
  exact some_spec h₃,
end

-- Exercise 214:
theorem sup_monotone (S T : set R) (h₁ : has_upper_bound S) (h₂ : has_upper_bound T)
(h₃ : S ≠ ∅) (h₄ : T ≠ ∅) : S ⊆ T → sup S ≤ sup T :=
begin
  have h₅ : ∀ (v : R), upper_bound v S → sup S ≤ v, from (sup_is_sup h₁ h₃).right,
  have h₆ : upper_bound (sup T) T, from (sup_is_sup h₂ h₄).left,
  intro k,
  sorry  
end

-- Exercise 215:
-- The exercise below is rather challenging.
theorem archimedean : ∀ x : R, ∃ n : ℕ, x < n :=
begin
  by_contra h,
  push_neg at h,
  cases h with x hx,
  let S := {m : R | ∃ n : ℕ, (m = n) ∧ (x ≥ n)},
  have h₁ : ↑1 ∈ S, from ⟨1, rfl, hx 1⟩,
  have h₂ : S ≠ ∅,
  { intro h, rw h at h₁, exact h₁, },
  have h₃ : has_upper_bound S,
  { use x, rintros _ ⟨_, rfl, xgen⟩, exact xgen, },
  have h₄ : is_sup (sup S) S, from sup_is_sup h₃ h₂,
  sorry  
end

-- Exercise 216:
-- Use `archimedean` and other results (such as `inv_pos` and `inv_lt_inv`) to prove:
theorem inv_lt_of_pos (ε : R) (h : 0 < ε) : ∃ n : ℕ, n ≠ 0 ∧ (↑n)⁻¹ < ε :=
begin
  sorry  
end

-- Exercise 217:
-- If a non-negative number is smaller than every positive number, it must be zero.
-- This *can* be proved without the completeness axiom, but the proof is more straightforward
-- (in my opinion) using the completeness axiom.
lemma zero_of_non_neg_of_lt_pos (a : R) (h : 0 ≤ a) (h₂ : ∀ ε > 0, a < ε) : a = 0 :=
begin
  sorry  
end

-- Exercise 218:
theorem bounded_iff_abs_lt (S : set R) : bounded S ↔ ∃ m : ℕ, ∀ s ∈ S, abs s < ↑m :=
begin
  split,
  { rintro ⟨⟨ub, hub⟩, lb, hlb⟩,
    rcases archimedean (max (abs ub) (abs lb)) with ⟨n, hn⟩,
    use n,
    intros s hs,
    unfold abs,
    cases max_choice s (-s) with hms hmns,
    { sorry, }, 
    { rw hmns,
      have h₂ : -s ≤ -lb, from neg_le_neg_iff.mpr (hlb s hs),
      have h₃ : -lb ≤ abs lb, from neg_le_abs lb,
      have h₄ : abs lb ≤ max (abs ub) (abs lb), from le_max_right _ _,
      apply lt_of_le_of_lt,
      { exact le_trans _ _ _ h₂ (le_trans _ _ _ h₃ h₄) },
      { exact hn, }, }, },
  { rintro ⟨m, hm⟩,
    split,
    { sorry, }, 
    { use (-m),
      intros s hs,
      rw [←neg_le_neg_iff, neg_neg],
      apply le_trans,
      { exact neg_le_abs s, },
      { exact le_iff_lt_or_eq.mpr (or.inl (hm s hs)), }, }, },
end

end myreal

end mth1001
