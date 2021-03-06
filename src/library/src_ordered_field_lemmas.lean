import .src_ordered_field tactic

namespace mth1001

namespace myreal

section ordered

variables {R : Type} [myordered_field R]

open_locale classical

open myordered_field

lemma pos_one : pos (1 : R) :=
begin
  rcases trichotomy (1 : R) with ⟨hpo, _, _ ⟩ | ⟨_, hoe, _ ⟩  | ⟨hnpo, hnoe, hpno⟩ ,
  { exact hpo, },
  { exact absurd hoe zero_ne_one.symm, },
  { exfalso, apply hnpo,
    convert pos_mul_of_pos_of_pos _ _ hpno hpno,
    rw [neg_mul_neg_self, one_mul], },
end

lemma pos_nat (n : ℕ) : n ≠ 0 → pos (n : R) :=
begin
  induction n with k hk,
  { intro _, contradiction, },
  { intro _,
    rw coe_nat_succ,
    by_cases h₁ : k = 0,
    { rw h₁,
      change pos((0 : R) + (1 : R)),
      rw zero_add,
      exact pos_one, },
    { exact pos_add_of_pos_of_pos _ _ (hk h₁) pos_one }, },
end

lemma lt_iff_pos_sub (x y : R) : x < y ↔ pos (y -x) := by refl

lemma lt_iff_pos_neg (x y : R) : x < y ↔ pos (y + -x) := by refl

lemma zero_lt_one' : (0 : R) < (1 : R) :=
begin
  rw [lt_iff_pos_sub, sub_zero],
  exact pos_one,
end


lemma gt_zero_mul_of_gt_zero_of_gt_zero {a b : R} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b :=
begin
  rw [lt_iff_pos_sub, sub_zero] at *,
  exact pos_mul_of_pos_of_pos a b h₁ h₂,
end

lemma mul_pos (a b : R) : 0 < a → 0 < b → 0 < a * b :=
begin
  intros h₁ h₂,
  rw [lt_iff_pos_sub, sub_zero] at *,
  exact pos_mul_of_pos_of_pos a b h₁ h₂,
end

lemma neg_pos {x : R} : 0 < -x ↔ x < 0:=
begin
  repeat {rw lt_iff_pos_neg},
  rw zero_add,
  have : -(0 : R) = (0 : R),
  { rw [←add_zero (-(0 : R) : R), neg_add], },
  rw [this, add_zero],
end

lemma trichotomy' (x y: R) : x < y ∧ ¬x = y ∧ ¬y < x ∨
                               ¬x < y ∧ x = y ∧ ¬y < x ∨
                               ¬x < y ∧ ¬x = y ∧ y < x :=
begin
  repeat {rw lt_iff_pos_sub},
  have : x - y = -(y - x),
  { rw [sub_eq_add_neg', sub_eq_add_neg', neg_add_eq_neg_add_neg', neg_neg], },
  rw this,
  rw [@eq_comm _ x y, (sub_eq_zero_iff_eq y x).symm],
  exact trichotomy (y + -x),
end

lemma lt_trans {x y z : R} : x < y → y < z → x < z :=
begin
  repeat {rw lt_iff_pos_sub},
  intros pyx pzy,
  have : z - x = (z - y) + (y - x),
  { repeat {rw sub_eq_add_neg'},
    rw [←add_assoc, add_assoc z _ _, neg_add, add_zero], },
  rw this,
  exact pos_add_of_pos_of_pos _ _ pzy pyx,
end

lemma add_lt_add_iff_right_mpr {x y : R} (z : R) : x < y → x + z < y + z :=
begin
  repeat {rw lt_iff_pos_sub},
  apply eq.substr,
  rw [sub_eq_add_neg', neg_add_eq_neg_add_neg', ←add_assoc],
  rw [add_assoc y, add_neg', add_zero, sub_eq_add_neg'],
end

lemma add_lt_add_iff_right_mp {x y : R} (z : R) : x + z < y + z → x < y :=
begin
  intro h,
  convert add_lt_add_iff_right_mpr (-z) h;
  rw [add_assoc, add_neg', add_zero],
end

lemma add_lt_add_iff_right {x y : R} (z : R) : x + z < y + z ↔ x < y :=
iff.intro (add_lt_add_iff_right_mp z) (add_lt_add_iff_right_mpr z)

theorem neg_lt_neg_iff  {a b : R} : -a < -b ↔ b < a :=
begin
  have h₁ : -a < -b ↔ -a + a < -b + a, from (add_lt_add_iff_right a).symm,
  have h₂ : b < a ↔ b + -a < a + -a, from (add_lt_add_iff_right (-a)).symm,
  have h₃ : -b + a = - (b + -a), 
  { rw [neg_add_eq_neg_add_neg', neg_neg, add_comm], },
  rw [h₁, h₂, neg_add, add_neg', h₃, neg_pos],
end

lemma mul_lt_mul_left_mpr {x y z : R} : 0 < z → x < y → z * x < z * y :=
begin
  repeat {rw lt_iff_pos_sub},
  rw [←mul_sub, sub_zero],
  exact pos_mul_of_pos_of_pos _ _,
end

theorem add_lt_add {a b c d : R} : a < b → c < d → a + c < b + d :=
begin
  repeat {rw lt_iff_pos_sub},
  intros h₁ h₂, 
  convert pos_add_of_pos_of_pos _ _ h₁ h₂,
  repeat {rw sub_eq_add_neg'},
  rw neg_add_eq_neg_add_neg',
  rw [add_assoc, add_comm (-c) (-a), ←add_assoc d, add_comm d (-a), add_assoc (-a), ←add_assoc],
end

lemma lt_irrefl {x : R} : ¬x < x :=
begin
  rcases (trichotomy' x x) with ⟨_, _, nxx⟩ | ⟨nxx, _⟩ | ⟨nxx, _⟩;
  exact nxx,
end

theorem ne_of_gt {a b : R} (h : b < a) : a ≠ b :=
λ k, lt_irrefl (@eq.subst _ (λ x, b < x) a b k h)

lemma le_iff_lt_or_eq {x y : R} : x ≤ y ↔ ((x < y) ∨ x = y) := by refl

lemma le_refl (x : R) : x ≤ x := or.inr rfl

lemma not_le_iff_lt (x y : R) : ¬(x ≤ y) ↔ (y < x) :=
begin
  rw le_iff_lt_or_eq,
  push_neg,
  rcases trichotomy' x y with ⟨hxlty, _, _⟩ | ⟨_, hxy, hnyltx ⟩  | ⟨hnxlty, hnxy, hxlty ⟩ ,
  { split,
    { rintro ⟨hnxy, _⟩,
      contradiction, },
    { intros hyltx, exfalso,
      exact lt_irrefl (lt_trans hxlty hyltx), }, },
  { split,
    { rintro ⟨_, hnxy⟩,
      contradiction, },
    { intro hyltx, contradiction, }, },
  { split,
    { intro _, exact hxlty, },
    { intro _, exact ⟨hnxlty, hnxy⟩, }, },
end

lemma not_lt_iff_le (x y : R) : ¬(x < y) ↔ (y ≤ x) :=
by rw [←not_le_iff_lt, not_not]


lemma lt_iff_le_not_le (a b : R) : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
begin
  rw [not_le_iff_lt, le_iff_lt_or_eq, or_and_distrib_right, and_self],
  exact ⟨λ h, or.inl h, λ h, or.elim h id (λ k, k.2)⟩,
end

lemma neg_nonneg {x : R} : 0 ≤ -x ↔ x ≤ 0 :=
begin
  repeat {rw le_iff_lt_or_eq},
  have k : 0 < -x ↔ x < 0, from neg_pos,
  split,
  { rintro (h₁ | h₂),
    { left, rwa ←k, },
    { right, rw [←neg_neg x, ←h₂, neg_zero], } },
  { rintro (h | rfl), 
    { left, rwa k, },
    { right, rw neg_zero, }, },
end

lemma le_trans (x y z : R) : x ≤ y → y ≤ z → x ≤ z :=
begin
  rintro (h₁ | rfl) (h₂ | rfl),
  { left, exact lt_trans h₁ h₂},
  { left, exact h₁ },
  { left, exact h₂, },
  { right, refl, },
end

lemma lt_of_le_of_lt {a b c : R} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
begin
  cases h₁ with altb aeqb,
  { exact lt_trans altb h₂, },
  { rw aeqb, exact h₂, }, 
end

lemma le_total (x y : R) : x ≤ y ∨ y ≤ x :=
begin
  rcases trichotomy' x y with ⟨xltx, _⟩ | ⟨_, xeqy, _⟩ | ⟨_, _, yltx⟩,
  { left, left, exact xltx, },
  { left, right, exact xeqy, },
  { right, left, exact yltx, },
end

lemma anti_symm (x y : R) : x ≤ y → y ≤ x → x = y :=
begin
  intros h₁ h₂,
  have h : (x ≠ y → false), -- Could do this using `by_contra`, but that's slow.
  { intro h,
    have h₃ : y < x := or.elim h₂ id (λ k, absurd k.symm h),
    have h₄ : x < y := or.elim h₁ id (λ k, absurd k h),
    exact lt_irrefl (lt_trans h₃ h₄), },
  rw [←(@not_not (x=y))],
  exact h,
end

theorem neg_le_neg_iff {a b : R} : -a ≤ -b ↔ b ≤ a :=
begin
  repeat {rw le_iff_lt_or_eq},
  split,
  { rintro (hlt | heq),
    { left, rwa ←neg_lt_neg_iff, },
    { right, rw [←neg_neg a, heq, neg_neg], }, },
  { rintro (hlt | heq),
    { left, rwa neg_lt_neg_iff, },
    { right, rw heq, }, },
end

theorem add_le_add {a b c d : R} : a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  rintro (h₁| rfl) (h₂ | rfl),
  { left, exact add_lt_add h₁ h₂ },
  { left, exact add_lt_add_iff_right_mpr c h₁, },
  { left, repeat {rw add_comm a _},
    exact add_lt_add_iff_right_mpr a h₂, },
  { exact le_refl _, },
end

theorem add_le_add_left (a b: R) : a ≤ b →  ∀ (c : R), c + a ≤ c + b :=
λ aleb c, add_le_add (le_refl c) aleb

theorem mul_self_non_neg (a : R) : 0 ≤ a * a:=
begin
  rcases trichotomy' 0 a with ⟨posa, _⟩ | ⟨_, eq0, _⟩ | ⟨_, _, nega⟩,
  { left,
    convert mul_lt_mul_left_mpr posa posa,
    rw mul_zero, },
  { right,
    rw [←eq0, mul_zero], },
  { left,
    rw ←neg_pos at nega,
    rw ←neg_mul_neg_self,
    convert mul_lt_mul_left_mpr nega nega,
    rw mul_zero, },
end

lemma non_neg_mul_of_non_neg_of_non_neg {a b : R} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b :=
begin
  cases h₁ with apos aeq0,
  { cases h₂ with bpos beq0,
    { left, exact gt_zero_mul_of_gt_zero_of_gt_zero apos bpos, },
    { right, rw [←beq0, mul_zero], }, },
  { right,
    rw [←aeq0, zero_mul], },
end

lemma non_neg_of_non_neg_mul_of_pos {x y : R} (h₁ : 0 ≤ x * y) (h₂ : 0 < x) : 0 ≤ y :=
begin
  cases h₁ with xlty xyeq0,
  { by_contra h₃,
    rw [not_le_iff_lt, ←neg_pos] at h₃,
    have h₄ : 0 < x * -y, from gt_zero_mul_of_gt_zero_of_gt_zero h₂ h₃,
    rw [←neg_mul_eq_mul_neg, neg_pos] at h₄,
    exact lt_irrefl (lt_trans h₄ xlty), },
  { right,
    rw mul_comm at xyeq0,
    symmetry,
    apply eq_zero_of_not_eq_zero_of_mul_not_eq_zero _ _ (ne_of_gt h₂) (xyeq0.symm), },
end

lemma non_neg_mul_iff_non_neg_and_non_neg_or_non_pos_and_non_pos (a b : R)
  : 0 ≤ a * b ↔ (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) :=
begin
  split,
  { intro h₁,
    by_cases h₂ : 0 ≤ a,
    { by_cases h₃ : a = 0,
      { rw h₃,
        exact or.elim (le_total b 0) (λ h₄, or.inr ⟨le_refl 0, h₄⟩) (λ h₄, or.inl ⟨le_refl 0, h₄⟩), },
      { have h₄ : 0 < a, from or.elim h₂ id (λ aeq0, absurd aeq0.symm h₃), 
        have h₅ : 0 ≤ b, from non_neg_of_non_neg_mul_of_pos h₁ h₄,
        exact or.inl ⟨or.inl h₄, h₅⟩, }, },
    { rw not_le_iff_lt at h₂,
      right,
      have k : b ≤ 0,
      { by_contra h₃,
        rw not_le_iff_lt at h₃,
        rw ←neg_pos at h₂,
        have h₄ : 0 < b * -a, from gt_zero_mul_of_gt_zero_of_gt_zero h₃ h₂,
        rw [←neg_mul_eq_mul_neg, mul_comm, neg_pos] at h₄,
        exact lt_irrefl (lt_of_le_of_lt h₁ h₄), },
      exact ⟨or.inl h₂, k⟩, }, },
  { rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩),
    { exact non_neg_mul_of_non_neg_of_non_neg h₁ h₂, },
    { rw ←neg_mul_neg a b,
      rw ←neg_nonneg at h₁ h₂,
      exact non_neg_mul_of_non_neg_of_non_neg h₁ h₂, }, },
end

theorem inv_pos {a : R}  (h : a ≠ 0) : 0 < a⁻¹ ↔ 0 < a :=
begin
  split,
  { intro k,
    have h₂ : 0 ≤ a * a, from mul_self_non_neg a,
    cases h₂ with posaa eq0,
    { convert mul_lt_mul_left_mpr k posaa,
      { rw mul_zero, },
      { rw [←mul_assoc, inv_mul a h, one_mul], }, },
    { have h₃ : a = 0,
      { cases eq_zero_or_eq_zero_of_mul_eq_zero a a eq0.symm;
        assumption, },
      exact absurd h₃ h, }, },
  { intro k,
    have h₂ : 0 ≤ (a⁻¹ * a⁻¹), from mul_self_non_neg a⁻¹,
    cases h₂ with posainvsq eq0,
    { convert mul_lt_mul_left_mpr k posainvsq,
      { rw mul_zero, },
      { rw [←mul_assoc, mul_inv a h, one_mul], }, },
    { have h₃ : a⁻¹ = 0,
      { cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ eq0.symm;
        assumption, },
      exact absurd h₃ (inv_ne_zero h), }, },
end

theorem inv_lt_inv {a b : R} (h₁ : 0  < a) (h₂ : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
begin
  split,
  { intro h₃,
    have h₄ : a * a⁻¹ < a * b⁻¹, from mul_lt_mul_left_mpr h₁ h₃, 
    have h₅ : a ≠ 0, from ne_of_gt h₁,
    rw (mul_inv a h₅) at h₄,
    have h₆ : b * 1 < b * (a * b⁻¹), from mul_lt_mul_left_mpr h₂ h₄,
    have h₇ : b ≠ 0, from ne_of_gt h₂,
    rw [mul_one, mul_comm, mul_assoc, inv_mul b h₇, mul_one] at h₆,
    exact h₆, },
  { intro h₃,
    have h₅ : a ≠ 0, from ne_of_gt h₁,
    have k₁ : a⁻¹ > 0, from (inv_pos h₅).mpr h₁,
    have h₄ : a⁻¹ * b < a⁻¹ * a, from mul_lt_mul_left_mpr k₁ h₃, 
    rw inv_mul a h₅ at h₄,
    have h₇ : b ≠ 0, from ne_of_gt h₂,
    have k₂ : b⁻¹ > 0, from (inv_pos h₇).mpr h₂,
    have h₆ :  b⁻¹ * (a⁻¹ * b) < b⁻¹ * 1, from mul_lt_mul_left_mpr k₂ h₄,
    rw [mul_comm, mul_assoc, mul_inv b h₇, mul_one, mul_one] at h₆,
    exact h₆, },
end

end ordered

section max_abs

variables {R : Type} [myordered_field R]

open_locale classical

open myordered_field

lemma le_max_right (a b : R) : b ≤ max a b :=
begin
  unfold max,
  by_cases h : b ≤ a,
  { rwa (if_pos h), },
  { rw (if_neg h),
    exact le_refl b, },
end

lemma le_max_left (a b : R) : a ≤ max a b :=
begin
  unfold max,
  by_cases h : b ≤ a,
  { rw (if_pos h),
    exact le_refl a, },
  { rw (if_neg h),
    rw not_le_iff_lt at h,
    left, exact h, },
end

lemma max_choice (a b : R) : max a b = a ∨ max a b = b :=
begin
  unfold max,
  by_cases h : b ≤ a,
  { rw (if_pos h), left, refl, },
  { rw (if_neg h),
    right, refl, },
end

lemma neg_le_abs (a : R) : -a ≤ abs a :=
begin
  unfold abs max,
  by_cases h : -a ≤ a,
  { rw (if_pos h), exact h, },
  { rw (if_neg h), exact le_refl (-a), },
end

lemma le_abs_self (a : R) : a ≤ abs a :=
begin
  unfold abs max,
  by_cases h : -a ≤ a,
  { rw (if_pos h), right, refl, },
  { rw (if_neg h), left,
    rw le_iff_lt_or_eq at h,
    push_neg at h,
    rw [not_lt_iff_le, le_iff_lt_or_eq, or_and_distrib_right] at h,
    rcases h with ⟨haltma, _⟩ | ⟨hama, hnama⟩,
    { exact haltma, },
    { exact absurd hama hnama.symm, }, },
end

theorem triangle_inequality (x y : R) : abs (x + y) ≤ abs x + abs y :=
begin
  by_cases h : -(x+y) ≤ x+y,
  { have : abs (x+y) = x + y,
    { unfold abs max,
      rw (if_pos h), },
    rw this,
    have h₁ : x ≤ abs x, from le_abs_self x,
    have h₂ : y ≤ abs y, from le_abs_self y,
    exact add_le_add h₁ h₂, },
  { have : abs (x+y) = -(x+y),
    { unfold abs max,
      rw (if_neg h), },
    rw this,
    rw [neg_add_eq_neg_add_neg', add_comm],
    have h₁ : -x ≤ abs x, from neg_le_abs x,
    have h₂ : -y ≤ abs y, from neg_le_abs y,
    exact add_le_add h₁ h₂, },
end

end max_abs

section upper_bounds

variables {R : Type} [myordered_field R]

theorem sup_uniqueness (S : set R) (a b : R) (h₁ : is_sup a S) (h₂ : is_sup b S) : a = b :=
anti_symm _ _ (h₁.right b h₂.left) (h₂.right a h₁.left)

theorem empty_set_upper_bound (u : R) : upper_bound u ∅ :=
λ s, (set.mem_empty_eq s) ▸ false.elim

end upper_bounds

section instance_linear_ordered_comm_ring

variables {R : Type} [myordered_field R]

instance : linear_ordered_comm_ring R :=
{ add               := comm_group.add,
  add_assoc         := comm_group.add_assoc,
  zero              := comm_group.zero,
  zero_add          := zero_add,
  add_zero          := add_zero,
  neg               := comm_group.neg,
  add_left_neg      := neg_add,
  add_comm          := comm_group.add_comm,
  mul               := myfield.mul,
  mul_assoc         := myfield.mul_assoc,
  one               := myfield.one,
  one_mul           := one_mul,
  mul_one           := myfield.mul_one,
  left_distrib      := myfield.mul_add,
  right_distrib     := add_mul,
  le                := le,
  lt                := lt,
  lt_iff_le_not_le  := lt_iff_le_not_le,
  le_refl           := le_refl,
  le_trans          := le_trans,
  le_antisymm       := anti_symm,
  add_le_add_left   := add_le_add_left,
  zero_ne_one       := myfield.zero_ne_one,
  mul_pos           := mul_pos,
  le_total          := le_total,
  zero_lt_one       := zero_lt_one',
  mul_comm          := myfield.mul_comm,
}

end instance_linear_ordered_comm_ring

end myreal

end mth1001