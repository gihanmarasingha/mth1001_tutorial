import .src_real_field
import .src_ordered_field_lemmas
import data.set.basic
import tactic

namespace mth1001

namespace myreal

open myreal_field myordered_field classical

open_locale classical

variables {R : Type} [myreal_field R]

def has_upper_bound (S : set R) := ∃ u : R, upper_bound u S

def has_lower_bound (S : set R) := ∃ v : R, lower_bound v S

lemma sup_is_sup {S : set R} (h₁ : has_upper_bound S) (h₂ : S ≠ ∅) : is_sup (sup S) S :=
begin
  have h₃ : ∃ x : R, is_sup x S, from completeness h₂ h₁,
  have h₄ : sup S = some h₃, from dif_pos h₃,
  rw h₄,
  exact some_spec h₃,
end

theorem sup_monotone (S T : set R) (h₁ : has_upper_bound S) (h₂ : has_upper_bound T)
(h₃ : S ≠ ∅) (h₄ : T ≠ ∅) : S ⊆ T → sup S ≤ sup T :=
begin
  have h₅ : ∀ (v : R), upper_bound v S → sup S ≤ v, from (sup_is_sup h₁ h₃).right,
  have h₆ : upper_bound (sup T) T, from (sup_is_sup h₂ h₄).left,
  intro k,
  apply h₅ (sup T),
  intros s hs,
  have ht : s ∈ T, from k hs,
  exact h₆ s ht,
end

theorem archimedean : ∀ x : R, ∃ n : ℕ, x < n :=
begin
  by_contra h,
  push_neg at h,
  cases h with x hx,
  let S := {m : R | ∃ n : ℕ, (m = n) ∧ (x ≥ n)},
  have h₁ : ↑1 ∈ S, from ⟨1, ⟨rfl, hx 1⟩⟩,
  have h₂ : S ≠ ∅,
  { intro h, rw h at h₁, exact h₁, },
  have h₃ : has_upper_bound S, from ⟨x, λ s ⟨n,hs,hn⟩, hs.symm ▸ hn⟩,
  have h₄ : is_sup (sup S) S, from sup_is_sup h₃ h₂,
  suffices k : upper_bound (sup S +- 1) S,
  { have k₂, from add_le_add (h₄.right (sup S + - 1) k) (le_refl (1 +- sup S)),
    have k₃ : sup S + (1 + -sup S) = 1, rw [add_comm 1 (-sup S), ←add_assoc, add_neg', zero_add],
    have k₄ : sup S +-1 + (1 + -sup S) = 0,
    { rw [add_assoc,  ←add_assoc (-1) 1 (-sup S), neg_add, zero_add, add_neg'], },
    rw [k₃, k₄, ←not_lt_iff_le] at k₂,
    apply k₂,
    rw [lt_iff_pos_neg, neg_zero, add_zero], exact pos_one, },
  rintros _ ⟨m, rfl, xgem⟩,
  have h₆ : ↑(m + 1) ∈ S, from  ⟨m+1, rfl, hx (m+1)⟩,
  convert (add_le_add (h₄.left (↑m + 1) h₆) (le_refl (-1))),
  rw [add_assoc,add_neg',add_zero],
end

theorem inv_lt_of_pos (ε : R) (h : 0 < ε) : ∃ n : ℕ, n ≠ 0 ∧ (↑n)⁻¹ < ε :=
begin
  cases archimedean ε⁻¹ with n hn,
  use n,
  have h₁ : ε ≠ 0, from ne_of_gt h,
  have h₂ : 0 <  ε⁻¹, from (inv_pos h₁).mpr h,
  rw ←inv_inv' ε h₁ ,
  have h₃ : (0 : R) < ↑n, from lt_trans h₂ hn,
  rw (inv_lt_inv h₃ h₂),
  split,
  { intro heq0,
    rw heq0 at h₃,
    exact lt_irrefl h₃, },
  { exact hn, },
end

lemma zero_of_non_neg_of_lt_pos (a : R) (h : 0 ≤ a) (h₂ : ∀ ε > 0, a < ε) : a = 0 :=
begin
  rw le_iff_lt_or_eq at h,
  cases h with hpos heq0,
  { rcases inv_lt_of_pos a hpos with ⟨n, hn0, hn⟩,
    have hnpos : pos (n : R), from pos_nat n hn0,
    have h₃ : (n : R) ≠ 0,
    { intro k, rw [k, ←add_neg' (0 : R), ←lt_iff_pos_neg] at hnpos,
      exact lt_irrefl hnpos, },
    have hninvpos : (0 : R) < (n : R)⁻¹,
    { rwa [(inv_pos h₃), lt_iff_pos_sub, sub_zero], },
    have h₄ : a < n⁻¹, from h₂ _ hninvpos,
    exfalso,
    exact lt_irrefl (lt_trans h₄ hn), },
  { exact heq0.symm, }
end

theorem bounded_iff_abs_lt (S : set R) : bounded S ↔ ∃ m : ℕ, ∀ s ∈ S, abs s < ↑m :=
begin
  split,
  { rintro ⟨⟨ub, hub⟩, lb, hlb⟩,
    rcases archimedean (max (abs ub) (abs lb)) with ⟨n, hn⟩,
    use n,
    intros s hs,
    unfold abs,
    cases max_choice s (-s) with hms hmns,
    { rw hms,
      have h₂ : s ≤ ub, from hub s hs,
      have h₃ : ub ≤ abs ub, from le_abs_self ub,
      have h₄ : abs ub ≤ max (abs ub) (abs lb), from le_max_left _ _,
      apply lt_of_le_of_lt,
      { exact le_trans _ _ _ h₂ (le_trans _ _ _ h₃ h₄)},
      { exact hn, }, },
    { rw hmns,
      have h₂ : -s ≤ -lb, from neg_le_neg_iff.mpr (hlb s hs),
      have h₃ : -lb ≤ abs lb, from neg_le_abs lb,
      have h₄ : abs lb ≤ max (abs ub) (abs lb), from le_max_right _ _,
      apply lt_of_le_of_lt,
      { exact le_trans _ _ _ h₂ (le_trans _ _ _ h₃ h₄) },
      { exact hn, }, }, },
  { rintro ⟨m, hm⟩,
    split,
    { use m,
      intros s hs,
      apply le_trans,
      { exact le_abs_self s, },
      { exact le_iff_lt_or_eq.mpr (or.inl (hm s hs)) }, },
    { use (-m),
      intros s hs,
      rw [←neg_le_neg_iff, neg_neg],
      apply le_trans,
      { exact neg_le_abs s, },
      { exact le_iff_lt_or_eq.mpr (or.inl (hm s hs)), }, }, },
end

end myreal

end mth1001