import ..library.src_real_field_lemmas
import ..library.src_ordered_field_lemmas
import data.set.basic
import tactic

namespace mth1001

namespace myreal

section upper_bound_of_subset

open myreal_field classical myordered_field

open_locale classical

variables {R : Type} [myreal_field R]

theorem upper_bound_of_subset {S T : set R} {u : R} (h₁ : S ⊆ T) (h₂ : upper_bound u T) 
: upper_bound u S :=
begin
  assume (s : R) (h : s ∈ S),
  have h₃ : s ∈ T, from h₁ h,
  exact h₂ s h₃,
end

example (S T : set R) : S ⊆ S ∪ T := set.subset_union_left S T
example (S T : set R) : T ⊆ S ∪ T := set.subset_union_right S T

example (S T : set R) (m₁ m₂ : R) (h₁ : has_upper_bound S) (h₂ : has_upper_bound T)
(h₃ : S ≠ ∅) (h₄ : T ≠ ∅) : is_sup (max (sup S) (sup T)) (S ∪ T) :=
begin
  let M := max (sup S) (sup T),
  cases (sup_is_sup h₁ h₃) with sups_ub sups_lub,
  cases (sup_is_sup h₂ h₄) with supt_ub supt_lub,
  split,
  { sorry, }, 
  { sorry, }, 
end

end upper_bound_of_subset

section infima

open myreal_field classical myordered_field

open_locale classical

variables {R : Type} [myreal_field R]

example (S : set R) : minus_set S = {x | -x ∈ S} := rfl

theorem lower_bound_iff_minus_upper_bound {S : set R} {v : R}
: lower_bound v S ↔ upper_bound (-v) (minus_set S) :=
begin
  split,
  { intros lubs s hsm,
    rw [←neg_neg s, neg_le_neg_iff],
    exact lubs (-s) hsm, },
  { intros ubms s hs,
    rw ←neg_le_neg_iff,
    rw ←neg_neg s at hs,
    exact ubms (-s) hs, },
end

theorem is_sup_minus_of_is_inf {S : set R} {v : R} : is_inf v S → is_sup (-v) (minus_set S) :=
begin
  rintro ⟨lb_S, hub⟩,
  have h₁ : upper_bound (-v) (minus_set S),
  { intros s hsm,
    rw [←neg_le_neg_iff, neg_neg],
    exact lb_S (-s) hsm, },
  have h₂ : ∀ x, upper_bound x (minus_set S) → (-v) ≤ x,
  { intros x hubms,
    rw [←neg_neg x, ←lower_bound_iff_minus_upper_bound] at hubms,
    rw [←neg_neg x, neg_le_neg_iff],
    exact hub (-x) hubms, },
  exact and.intro h₁ h₂,
end

theorem is_inf_of_is_sup_minus {S : set R} {v : R} : is_sup (-v) (minus_set S) → is_inf v S :=
begin
  rintro ⟨lb_mS, hub⟩,
  have h₁ : lower_bound v S,
  { intros s hs,
    rw ←neg_le_neg_iff,
    rw ←neg_neg s at hs,
    exact lb_mS (-s) hs, },
  have h₂ : ∀ x, lower_bound x S → x ≤ v,
  { intros x hlbs,
    rw lower_bound_iff_minus_upper_bound at hlbs,
    rw ←neg_le_neg_iff,
    exact hub (-x) hlbs, },
  exact and.intro h₁ h₂,
end

theorem is_inf_iff_is_sup_minus {S : set R} {v : R} : is_inf v S ↔ is_sup (-v) (minus_set S) :=
⟨is_sup_minus_of_is_inf, is_inf_of_is_sup_minus⟩

lemma is_sup_sup_minus_of_has_lb_nonempty {S : set R} (h₁ : has_lower_bound S) (h₂ : S ≠ ∅)
: is_sup (sup (minus_set S)) (minus_set S) :=
begin
  cases h₁ with v hv,
  have k₁ : upper_bound (-v) (minus_set S), from lower_bound_iff_minus_upper_bound.mp hv,
  have k₂ : has_upper_bound (minus_set S), from ⟨-v, k₁⟩,
  have k₃ : (minus_set S) ≠ ∅,
  { rw set.ne_empty_iff_nonempty at *,
    cases h₂ with s hs,
    use (-s),
    rw ←neg_neg s at hs,
    exact hs, },
  exact sup_is_sup k₂ k₃,
end

lemma inf_is_inf {S : set R} (h₁ : has_lower_bound S) (h₂ : S ≠ ∅) : is_inf (inf S) S :=
begin
  have h₂ : is_sup (sup (minus_set S)) (minus_set S) := is_sup_sup_minus_of_has_lb_nonempty h₁ h₂,
  rw [←neg_neg (sup (minus_set S)), ←is_inf_iff_is_sup_minus] at h₂,
  have h₃ : ∃ x, is_inf x S, from ⟨-sup(minus_set S), h₂⟩,
  have h₄ : inf S = some h₃, from dif_pos h₃,
  rw h₄,
  exact some_spec h₃,
end

lemma inf_eq_minus_sup {S : set R} (h₁ : has_lower_bound S) (h₂ : S ≠ ∅)
: inf S = -(sup (minus_set S)) :=
begin
  have h₃ : is_inf (inf S) S, from inf_is_inf h₁ h₂,
  have h₄ : is_sup (-(inf S)) (minus_set S), rwa is_inf_iff_is_sup_minus at h₃,
  have h₅ : is_sup (sup (minus_set S)) (minus_set S) := is_sup_sup_minus_of_has_lb_nonempty h₁ h₂,
  have h₆ : -(inf S) = sup (minus_set S), from sup_uniqueness (minus_set S) _ _ h₄ h₅,
  rw [←h₆, neg_neg],
end

end infima

end myreal

end mth1001
