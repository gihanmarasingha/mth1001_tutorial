import ..library.src_real_field_lemmas
import ..library.src_ordered_field_lemmas
import data.set.basic
import tactic

/-
There are no explicit exercises in this file, though you may choose to prove examples yourself.
The aim of this file is to prove that there is a real number whose square is 2.
-/

namespace mth1001

namespace myreal

section auxiliary

open myreal_field classical myordered_field

open_locale classical

variables {R : Type} [myreal_field R]

lemma difference_of_two_squares (x y : R) : x*x - y*y = (x - y)*(x+y) :=
begin
  rw mul_add,
  repeat { rw sub_eq_add_neg' <|> rw add_mul },
  rw [←neg_neg (x*y), neg_mul_eq_mul_neg x y, mul_comm x (-y), add_assoc, ←add_assoc (-y*x) _ _],
  rw [add_neg', zero_add, neg_mul_eq_mul_neg, mul_comm y (-y)],
end

lemma square_le_square_iff_le_of_non_neg_of_non_neg (a b : R) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b)
: a*a ≤ b*b ↔ a ≤ b :=
begin
  split,
  { intro aalebb,
    have h₃ : 0 ≤ b*b - a*a, linarith,
    rw difference_of_two_squares b a at h₃,
    rw non_neg_mul_iff_non_neg_and_non_neg_or_non_pos_and_non_pos at h₃,
    cases h₃; linarith },
  { intro aleb,
    exact mul_le_mul aleb aleb h₁ h₂, },
end

lemma pos_mul_iff_pos_and_pos_or_neg_and_neg (a b : R)
  : 0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) :=
begin
  split,
  { intro h,
    by_cases h₂ : 0 ≤ a,
    { by_cases h₃ : a = 0,
      { rw h₃ at h, linarith, },
      { have h₄ : 0 < a, from or.elim h₂ id (λ aeq0, absurd aeq0.symm h₃), 
        have h₅ : 0 < b, from (zero_lt_mul_left h₄).mp h,
        exact or.inl ⟨h₄, h₅⟩, }, },
    { have h₄ : a < 0, linarith,
      have h₅ : b < 0, 
      { by_contra p,
        rw not_lt_iff_le at p,
        rw ←neg_pos at h₄,
        have h₅ : 0 ≤ (-a) * b, from (zero_le_mul_left h₄).mpr p,
        have h₆ : -a * b = -(a*b),
        { rw [mul_comm (-a), ←neg_mul_eq_mul_neg, mul_comm], },
        rw h₆ at h₅,
        linarith, },
        exact or.inr ⟨h₄, h₅⟩, }, },
  { rintro (⟨apos, bpos⟩ | ⟨aneg, bneg⟩),
    { exact gt_zero_mul_of_gt_zero_of_gt_zero apos bpos },
    { rw ←neg_mul_neg a b,
      rw ←neg_pos at aneg bneg,
      exact gt_zero_mul_of_gt_zero_of_gt_zero aneg bneg, }, },
end

lemma square_lt_square_iff_lt_of_pos_of_pos (a b : R) (h₁ : 0 < a) (h₂ : 0 < b)
: a*a < b*b ↔ a < b :=
begin
  split,
  { intro aalebb,
    have h₃ : 0 < b*b - a*a, linarith,
    rw difference_of_two_squares b a at h₃,
    rw pos_mul_iff_pos_and_pos_or_neg_and_neg at h₃,
    rcases h₃ with ⟨h₃_left, h₃_right⟩ | ⟨h₃_left, h₃_right⟩,
    { linarith, },
    { have h₄ : a < -b, linarith,
      have h₅ : -b < 0, linarith,
      have h₆ : a < 0, from lt_trans h₄ h₅,
      have : (0 : R) < 0, from lt_trans h₁ h₆, 
      linarith, }, },
  { intro aleb,
    apply mul_lt_mul,
    { exact aleb, },
    { exact le_of_lt aleb, },
    { exact h₁ },
    { exact le_of_lt h₂ }, },
end

lemma zero_eq_zero : (0 : R) = ↑0 := rfl

lemma one_eq_one : ↑1 = (1 : R) :=
by rw [coe_nat_succ, ←zero_eq_zero, zero_add]

lemma pos_iff_gt_zero (x : R) : pos x ↔ 0 < x := 
by rw [lt_iff_pos_sub, sub_zero]

lemma non_zero_of_pos {x : R} (h : 0 < x) : x ≠ 0 :=
begin
  intro k,
  rw k at h,
  exact lt_irrefl h,
end

lemma coe_zero_inj {m : ℕ} (h : (m : R) = 0) : m = 0 :=
begin
  by_contra k,
  have h₂ : pos(m : R), from pos_nat m k,
  rw [h, pos_iff_gt_zero (0 : R)] at h₂,
  exact lt_irrefl h₂,
end

lemma coe_non_zero_of_non_zero {m : ℕ} (h : m ≠ 0) : (m : R) ≠ 0 :=
begin
  contrapose! h,
  exact coe_zero_inj h,
end

lemma gt_zero_of_ne_zero_nat (n : ℕ) (h : n ≠ 0) : (0 : R) < n :=
begin
  rw [←pos_iff_gt_zero],
  exact pos_nat n h,
end

lemma coe_pred (n : ℕ) (h : n ≠ 0) : (↑(n-1) : R) = ↑n - 1 :=
begin
  induction n with k hk,
  { exfalso, apply h, refl, },
  { have : nat.succ k - 1 = k := rfl,
    rw [this, coe_nat_succ, sub_eq_add_neg', add_assoc, add_neg', add_zero ], },
end

lemma coe_pred_eq_of_coe_succ_eq {x k : ℕ} (h : ↑x = ↑k + (1 : R)) : (↑(x-1) : R)= ↑k :=
begin
  by_cases xeq0 : x = 0,
  { exfalso, rw xeq0 at h, 
    change 0 = ↑k + (1:R) at h,
    have h₂ : ↑k = -(1 : R),
    { rw [←zero_add (-1: R), h, add_assoc, add_neg', add_zero], },
    have h₃ : (0 : R) ≤ ↑k,
    { rw le_iff_lt_or_eq,
      by_cases h₄ : k = 0,
      { rw h₄, right, refl, },
      { left, rw ←pos_iff_gt_zero, exact pos_nat k h₄, }, },
    rw h₂ at h₃,
    linarith, },
  { change x ≠ 0 at xeq0,
    rw coe_pred _ xeq0,
    linarith, }
end

lemma coe_inj (m n : ℕ) (h : (m : R) = (n : R)) : m = n :=
begin
  revert m,
  induction n with k hk,
  { intro m, exact coe_zero_inj, },
  { intros x hx,
    rw coe_nat_succ at hx,
    specialize hk (x-1),
    by_cases h₂ : x = 0,
    { rw [h₂, ←zero_eq_zero] at hx,
      have h₂ : ↑k = -(1 : R),
      { rw [←zero_add (-1: R), hx, add_assoc, add_neg', add_zero], },
      have h₃ : (0 : R) ≤ ↑k,
      { rw le_iff_lt_or_eq,
        by_cases h₄ : k = 0,
        { rw h₄, right, refl, },
        { left, rw ←pos_iff_gt_zero, exact pos_nat k h₄, }, },
      rw h₂ at h₃,
      linarith, },
    { rw coe_pred x h₂ at hk, 
      have h₃ : ↑x - (1 : R) = ↑k, linarith,
      have h₄ : x - 1 = k, from hk h₃,
      rw ←h₄,
      cases nat.eq_zero_or_eq_succ_pred x with x0 xsp,
      { exact absurd x0 h₂, },
      { assumption, }, }, },
end

lemma coe_monotone (m n : ℕ) (h : m ≤ n) : (m : R) ≤ (n : R) :=
begin
  revert n,
  induction m with k hk,
  { intros n h,
    rw [←zero_eq_zero,le_iff_lt_or_eq],
    by_cases h₂ : n = 0,
    { right, rw [h₂, zero_eq_zero], },
    { left, exact gt_zero_of_ne_zero_nat n h₂, }, },
  { intros x hx,
    specialize hk (x-1),
    by_cases h₂ : x = 0,
    { exfalso,
      rw [h₂, ←not_lt] at hx,
      exact hx (nat.succ_pos k), },
    { rcases nat.exists_eq_succ_of_ne_zero h₂ with ⟨w, h⟩,
      rw coe_nat_succ,
      rw coe_pred x h₂ at hk,
      rw h at hx hk,
      suffices h₃ : ↑k ≤ ↑(nat.succ w) - (1 : R),
      { rw h, linarith, },
      have h₃ : nat.succ w - 1 = w := rfl,
      rw h₃ at hk,
      rw ←nat.pred_le_iff at hx,
      change k ≤ w at hx,
      exact hk hx, }, },
end

lemma coe_monotone' (m n : ℕ) (h : m < n) : (m : R) < (n : R) :=
begin
  have h₂ : m ≤ n, linarith,
  have h₃ : (m : R) ≤ n, from coe_monotone _ _ h₂,
  rw le_iff_lt_or_eq at h₃,
  cases h₃ with mltn meqn,
  { exact mltn, },
  { have h₃ : m = n, from coe_inj m n meqn, 
    linarith, },
end

lemma non_neg_of_non_neg (n : ℕ) (h : 0 ≤ n) : (0 : R) ≤ ↑n :=
begin
  rw le_iff_lt_or_eq,
  by_cases h₂ : n = 0,
  { right, rw [h₂, zero_eq_zero], },
  { left, exact gt_zero_of_ne_zero_nat n h₂, }
end

lemma ge_one_of_non_zero (k : ℕ) (h : k ≠ 0): (1 : R) ≤ k :=
begin
  induction k with m hm,
  { exfalso,
    apply h, refl, },
  { rw coe_nat_succ m,
    conv {to_lhs, rw ←add_zero (1 : R)},
    by_cases h₂ : m = 1,
    { rw [h₂, add_zero, one_eq_one], 
      change (1 : R) ≤ 2,
      rw le_iff_lt_or_eq,
      left,
      linarith, },
    { rw add_comm,
      apply add_le_add,
      { rw le_iff_lt_or_eq,
        by_cases h₃ : m = 0,
        { right, rw h₃, refl, },
        { left, exact gt_zero_of_ne_zero_nat m h₃, }, },
      { exact le_refl 1, }, }, },
end

lemma pos_inv_nat_of_non_zero {n : ℕ} (h : n ≠ 0) : (0 : R) < (↑n)⁻¹ :=
begin
  have h₂ : (0 : R) < ↑n, from gt_zero_of_ne_zero_nat n h,
  have h₃ : ↑n ≠ (0 : R), from non_zero_of_pos h₂,
  rwa inv_pos h₃,
end

theorem inv_le_inv {a b : R} (h₁ : 0 < a) (h₂ : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
begin
  have k₁ : a ≠ (0 : R), from non_zero_of_pos h₁,
  have k₂ : b ≠ 0, from non_zero_of_pos h₂,
  repeat {rw le_iff_lt_or_eq },
  split,
  { rintro (hlt | heq),
    { left,
      rwa ←inv_lt_inv h₁ h₂, },
    { right,
      rw [←inv_inv' a k₁, ←inv_inv' b k₂, heq], }, },
  { rintro (hlt | heq),
    { left, 
      rwa inv_lt_inv h₁ h₂, },
    { rw heq, right, refl, }, },
end

lemma pos_add_inv_nat_of_pos {u : R} {n : ℕ} (h : (0 : R) < u) (h₂ : n ≠ 0)
: (0 : R) < u + (↑n)⁻¹ :=
begin
  rw ←add_zero (0 : R),
  apply add_lt_add h,
  rw inv_pos (coe_non_zero_of_non_zero h₂),
  exact gt_zero_of_ne_zero_nat n h₂,
end

lemma pos_sub_inv_nat_of_pos {u : R} {n : ℕ} (k₄ : (0 : R) < u) (ne0 : n ≠ 0) (k₅ : 2 < u*u)
: (0 : R) < u - (↑n)⁻¹ :=
begin
  by_contra p, 
  have : u ≤ (↑n)⁻¹, linarith,
  have h₂ : (1 : R) ≤ (↑n), from ge_one_of_non_zero n ne0,
  have h₃ : (0 : R) < ↑n, {rw ←pos_iff_gt_zero, exact pos_nat n ne0},
  have h₄ : (↑n)⁻¹ ≤ (1 : R)⁻¹, { rwa inv_le_inv h₃ zero_lt_one, },
  have h₅ : u ≤ (1 : R)⁻¹, linarith,
  rw one_inv at h₅,
  have : u * u ≤ 1 * 1, from mul_le_mul h₅ h₅ (le_of_lt k₄) zero_le_one,
  linarith,
end


lemma lt_sub_inv_nat {u : R} {n : ℕ} (h₂ : n ≠ 0)
: u - (↑n)⁻¹ < u:=
begin
  rw [sub_eq_add_neg', add_lt_iff_neg_left, neg_lt_zero, inv_pos (coe_non_zero_of_non_zero h₂)],
  exact gt_zero_of_ne_zero_nat n h₂,
end

end auxiliary

namespace sqrt_two

open myreal_field classical myordered_field

open_locale classical

variables {R : Type} [myreal_field R]

lemma has_upper_bound_S : has_upper_bound ({x : R | (0 < x) ∧ (x*x < 2)} : set R) :=
begin
  use (2 : R),
  intros s hs,
  cases hs with h₁ h₂, -- `h₁ : 0 < s`, `h₂ : s * s < 2`, 
  have h₄ : (2 : R) < 2 * 2, linarith,
  have h₅ : s * s < 2*2,
  { apply lt_trans h₂ h₄, },
  have : s * s ≤ 2*2, from le_of_lt h₅,
  have h₆ : 0 < (2 : R), linarith,
  have h₇ : 0 ≤ (2 : R), from le_of_lt h₆,
  rwa ←square_le_square_iff_le_of_non_neg_of_non_neg _ _ (le_of_lt h₁) h₇,
end 

lemma one_in_S : (1 : R) ∈ {x : R | (0 < x) ∧ (x*x < 2)} :=
⟨by linarith, by linarith⟩

lemma non_empty_S : ({x : R | (0 < x) ∧ (x*x < 2)} : set R) ≠ ∅ :=
begin
  have h : (1 : R) ∈ {x : R | (0 < x) ∧ (x*x < 2)}, from one_in_S,
  intro h₂,
  rw h₂ at h,
  exact h,
end

lemma not_upper_bound_of_exists_nat {u : R} {S : set R} (h : ∃ n : ℕ, n ≠ 0 ∧ (u + (↑n)⁻¹ ∈ S))
: ¬(upper_bound u S) :=
begin
  rcases h with ⟨n, ne0, hn⟩,
  unfold upper_bound,
  push_neg,
  use (u + (↑n)⁻¹),
  apply and.intro hn,
  suffices h : (0 : R) + u< (↑n)⁻¹ + u,
  { rwa [zero_add, add_comm] at h,},
  apply add_lt_add_iff_right_mpr,
  have h₂ : (0 : R) < n, from gt_zero_of_ne_zero_nat n ne0,
  rwa inv_pos (coe_non_zero_of_non_zero ne0),
end

lemma not_lub_of_exists_nat {u : R} {S : set R} (h : ∃ n : ℕ, n ≠ 0 ∧ (upper_bound (u - (↑n)⁻¹) S))
: ¬(∀ v : R, upper_bound v S → u ≤ v) :=
begin
  rcases h with ⟨n, ne0, hn⟩,
  push_neg,
  use (u - (↑n)⁻¹),
  exact and.intro hn (lt_sub_inv_nat ne0),
end

def S : set R := {x : R | (0 < x) ∧ (x*x < 2)}

section lemmas_for_ub_contra

lemma pos_sub_inv_nat_of_pos {u : R} {n : ℕ} (k₄ : (0 : R) < u) (ne0 : n ≠ 0) (k₅ : 2 < u*u)
: (0 : R) < u - (↑n)⁻¹ :=
begin
  by_contra p, 
  have : u ≤ (↑n)⁻¹, linarith,
  have h₂ : (1 : R) ≤ (↑n), from ge_one_of_non_zero n ne0,
  have h₃ : (0 : R) < ↑n, {rw ←pos_iff_gt_zero, exact pos_nat n ne0},
  have h₄ : (↑n)⁻¹ ≤ (1 : R)⁻¹, { rwa inv_le_inv h₃ zero_lt_one, },
  have h₅ : u ≤ (1 : R)⁻¹, linarith,
  rw one_inv at h₅,
  have : u * u ≤ 1 * 1, from mul_le_mul h₅ h₅ (le_of_lt k₄) zero_le_one,
  linarith,
end

lemma sq_add_inv_ub {u : R} {k : ℕ} (h : k ≠ 0)
: (u + (↑k)⁻¹)*(u + (↑k)⁻¹) ≤ u*u + (2*u+1)*(↑k)⁻¹ :=
begin
  rw [add_mul, add_mul, mul_add, mul_add, mul_comm (↑k)⁻¹ u, one_mul, add_assoc],
  apply add_le_add (le_refl (u* u)),
  rw [←add_assoc, ←two_mul, ←mul_assoc],
  apply add_le_add (le_refl _),
  have h₂ : (k : R) ≠ 0, from coe_non_zero_of_non_zero h,
  suffices h : (↑k)⁻¹ * (↑k)⁻¹ ≤ (↑k)⁻¹ * (1 : R),
  { rwa mul_one at h, },
  have h₃ : (1 : R) ≤ (↑k), from ge_one_of_non_zero k h,
  have h₄ : (↑k)⁻¹ ≤ (1 : R),
  { rwa [←one_inv, inv_le_inv (gt_zero_of_ne_zero_nat k h) (zero_lt_one : (0 : R) < 1)], },
  have h₅ : (0 : R) < (↑k)⁻¹, from pos_inv_nat_of_non_zero h,
  exact mul_le_mul (le_refl (↑k)⁻¹) h₄ (le_of_lt h₅) (le_of_lt h₅),
end

lemma inequ1 {u : R} (h₁ : 0 < u) (h₂ : u*u < 2) : (0 : R) < (2*u + 1)⁻¹ * (2 - u*u) :=
begin
  have h₃ : 0 < 2 - u * u, linarith,
  have h₄ : 0 < 2 * u + 1, from add_pos (by linarith) (by linarith),
  have h₅ : 2*u+ 1 ≠ 0, linarith,
  have h₆ : 0 < (2*u + 1)⁻¹, from (inv_pos h₅).mpr h₄,
  exact mul_pos _ _ h₆ h₃,
end

lemma inequ2 {u : R} {n : ℕ} (h₁ : 0 < u) (h₂ : (↑n)⁻¹ < (2 * u + 1)⁻¹ * (2 - u * u))
: u * u +  (2 * u + 1) * (↑n)⁻¹ < 2:=
begin
  suffices h : ((2 : R)*u+1) * (↑n)⁻¹ < (2- u * u), linarith,
  have h₄ : 0 < 2 * u + 1, from add_pos (by linarith) (by linarith),
  have h₅ : 2*u+ 1 ≠ 0, linarith,
  suffices h : (2 * u + 1) * (↑n)⁻¹ < (2 * u + 1) * ((2*u + 1)⁻¹ * (2 - u * u)),
  { rwa [←mul_assoc, mul_inv _ h₅, one_mul] at h, },
  exact mul_lt_mul_left_mpr h₄ h₂,
end

lemma ub_contra {u : R} (k₃ : upper_bound u S) (k₄ : (0 : R) < u) (k₅ : u * u < 2) : u * u = 2 :=
begin
  suffices h : ¬(upper_bound u S), from absurd k₃ h,
  suffices h : ∃ n : ℕ, (n ≠ 0) ∧ u + (↑n)⁻¹ ∈ S, from not_upper_bound_of_exists_nat h,
  suffices h : ∃ n : ℕ, (n ≠ 0) ∧ ((u + (n : R)⁻¹) * (u + (↑n)⁻¹) < 2),
  { rcases h with ⟨n, ne0, hn⟩,
    exact ⟨n, ne0, pos_add_inv_nat_of_pos k₄ ne0, hn⟩, },
  suffices h : ∃ n : ℕ, n ≠ 0 ∧ (u*u + ((2 : R)*u + 1)*(↑n)⁻¹) < 2,
  { rcases h with ⟨n, ne0, hn⟩,
    exact ⟨n, ne0, (lt_of_le_of_lt) (sq_add_inv_ub ne0) hn⟩, },
  have k₆ : (0 : R) < (2*u + 1)⁻¹ * (2 - u*u) := inequ1 k₄ k₅,
  rcases (inv_lt_of_pos _ k₆) with ⟨n, ne0, h₂⟩,
  exact ⟨n, ne0, (inequ2 k₄ h₂)⟩,
end

end  lemmas_for_ub_contra

section lemmas_for_lub_contra

lemma sq_sub_inv_ub {u : R} {k : ℕ} (h₁ : 0 < u) (h₂ : k ≠ 0)
: (u - (↑k)⁻¹) * (u - (↑k)⁻¹) > u*u - 2*u*(↑k)⁻¹ :=
begin
  repeat {rw sub_eq_add_neg},
  rw [mul_add, add_mul, add_mul, mul_comm (-(↑k)⁻¹) u, add_assoc],
  apply add_lt_add_of_le_of_lt(le_refl (u* u)),
  rw [←add_assoc, ←two_mul, neg_mul_eq_mul_neg, mul_assoc, lt_add_iff_pos_right, neg_mul_neg_self],
  exact mul_pos _ _ (pos_inv_nat_of_non_zero h₂) (pos_inv_nat_of_non_zero h₂),
end

lemma lub_contra_subproof1 {u : R} (k₄ : (0 : R) < u) (k₅ : 2 < u * u)
(h : ∃ n : ℕ, (n ≠ 0) ∧ (2 < (u - (n : R)⁻¹) * (u - (↑n)⁻¹))) 
: ∃ (n : ℕ), n ≠ 0 ∧ upper_bound (u - (↑n)⁻¹) S :=
begin
  rcases h with ⟨n, ne0, hn⟩,
  use n,
  apply and.intro ne0,
  intros x hx,
  cases hx with xpos xsqlt2,
  have h₃ : x * x < (u - (n : R)⁻¹) * (u - (↑n)⁻¹), from lt_trans xsqlt2 hn,
  rw le_iff_lt_or_eq,
  left,
  exact (square_lt_square_iff_lt_of_pos_of_pos _ _ xpos (pos_sub_inv_nat_of_pos k₄ ne0 k₅)).mp h₃,
end

lemma inequ3 {u : R} {n : ℕ} (h₁ : 0 < u) (h₂ : (↑n)⁻¹ < (2*u)⁻¹ * (u*u - 2))
: 2 < u * u - 2 * u * (↑n)⁻¹ :=
begin
  suffices h : 2 * u * (↑n)⁻¹  < u * u - 2, linarith,
  have h₄ : 0 < (2 * u), linarith,
  have h₅ : 2 * u ≠ 0, linarith,
  suffices h : (2 * u) * (↑n)⁻¹ < (2 * u) * ( (2*u)⁻¹ *(u*u -2)),
  { rwa [←mul_assoc, mul_inv _ h₅, one_mul] at h, },
  exact mul_lt_mul_left_mpr h₄ h₂,
end

lemma inequ4 {u : R} (h₁ : 0 < u) (h₂ : 2 < u * u) : 0 < (2*u)⁻¹ * (u * u - 2):=
begin
  have h₃ : 0 < u * u - 2, linarith,
  have h₄ : 0 < 2 * u, linarith,
  have h₅ : 2*u  ≠ 0, linarith,
  have h₆ : 0 < (2*u)⁻¹, from (inv_pos h₅).mpr h₄,
  exact mul_pos _ _ h₆ h₃,
end

lemma lub_contra {u : R} (k₃ : ∀ v : R, upper_bound v S → u ≤ v) (k₄ : (0 : R) < u)
(k₅ : 2 < u * u)
: u * u = 2 :=
begin
  suffices h : ¬(∀ v : R, upper_bound v S → u ≤ v), from absurd k₃ h,
  suffices h : ∃ n : ℕ, n ≠ 0 ∧ (upper_bound (u - (↑n)⁻¹) S), from not_lub_of_exists_nat h,
  suffices h : ∃ n : ℕ, (n ≠ 0) ∧ (2 < (u - (n : R)⁻¹) * (u - (↑n)⁻¹)),
  from lub_contra_subproof1 k₄ k₅ h,
  suffices h : ∃ n : ℕ, n ≠ 0 ∧ 2  < u * u - 2 * u * (↑n)⁻¹,
  { rcases h with ⟨n, ne0, hn⟩,
    exact ⟨n, ne0, lt_trans hn (sq_sub_inv_ub k₄ ne0)⟩ },
  suffices h : ∃ n : ℕ, n ≠ 0 ∧ (↑n)⁻¹ < (2*u)⁻¹ * (u*u - 2),
  { rcases h with ⟨n, ne0, hn⟩,
    exact ⟨n, ne0, inequ3 k₄ hn⟩, },
  have k₆ : 0 < (2*u)⁻¹ * (u * u - 2):= inequ4 k₄ k₅,
  exact inv_lt_of_pos _ k₆,
end

end lemmas_for_lub_contra

lemma sqrt_two_exists : (sup S)*(sup S) = (2 : R) :=
begin
  have k₂ : ({x : R | (0 < x) ∧ (x*x < 2)} : set R) ≠ ∅, from non_empty_S,
  have k₃ : is_sup (sup S) S, from  sup_is_sup has_upper_bound_S k₂,
  have k₄ : ↑0 < sup S,
  { suffices h : (1 : R) ≤ sup S,
    { change (0 : R) < sup S,
      exact lt_of_lt_of_le zero_lt_one h, },
    exact k₃.left (1 : R) one_in_S, },
  rcases trichotomy' ((sup S)*(sup S)) (2 : R) with ub | sq_eq | lub,
  { exact ub_contra k₃.left k₄ ub.left, },
  { exact sq_eq.right.left, },
  { exact lub_contra k₃.right k₄ lub.right.right, },
end

end sqrt_two

end myreal

end mth1001
