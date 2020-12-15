import .src_field tactic

namespace mth1001

namespace myreal

section grouplaws

variables {R : Type} [comm_group R]

lemma add_comm (x y : R) : x + y = y + x := comm_group.add_comm x y
lemma add_assoc (x y z : R) : (x + y) + z = x + (y + z) := comm_group.add_assoc x y z
lemma add_zero (x : R) : x + 0 = x := comm_group.add_zero x
lemma zero_add (x : R) : 0 + x = x := by {rw [add_comm, add_zero]}
lemma add_neg' (x : R) : x + (-x) = 0 := comm_group.add_inv x
lemma neg_add (x : R) : (-x) + x = 0 := by {rw [add_comm, add_neg']}

def add_identity (u : R) := ∀ x : R, (x + u = x) ∧ (u + x = x)

lemma add_left_eq_self_mp {x a : R} : x + a = a → x = 0 :=
by { intro h, rw [←(add_zero x), ←(add_neg' a), ←add_assoc, h] }

lemma add_left_eq_self_mpr {x a : R} : x = 0 → x + a = a :=
by { intro h, rw [h, zero_add] }

theorem add_left_eq_self (x a : R) : x + a = a ↔ x = 0:=
iff.intro add_left_eq_self_mp add_left_eq_self_mpr

theorem add_left_inj  (x a b : R) : a + x = b + x ↔ a = b :=
⟨ λ h, by rw [←(add_zero a), ←(add_neg' x), ←add_assoc, h, add_assoc, add_neg' x, add_zero],
  λ h, h ▸ rfl⟩

lemma sub_eq_add_neg' (x y : R) : x - y = x + (-y) := rfl 

lemma neg_zero : -(0 : R) = 0 :=
by rw [←add_zero (-(0 : R)), neg_add]

lemma sub_zero (a : R) : a - 0 = a :=
by rw [sub_eq_add_neg', neg_zero, add_zero]

theorem sub_eq_zero_iff_eq (x y : R) : x - y = 0 ↔ x = y :=
by rw [←add_left_inj (y) _ _, zero_add, sub_eq_add_neg', add_assoc, neg_add, add_zero]

theorem neg_neg (x : R) : - - x = x :=
by rw [←(zero_add (- - x)), ←(add_neg' x), add_assoc, add_neg', add_zero]

lemma neg_add_eq_neg_add_neg' (x y : R) : -(x + y) = -y + - x :=
begin
  rw [←add_zero (-(x+y)), ←add_neg' x],
  conv in (x + -x) { congr, rw ←add_zero x, skip },
  rw [←add_neg' y, ←add_assoc x y _, add_assoc (x+y) _ _, ←add_assoc, neg_add, zero_add],
end

end grouplaws

section fieldlaws

variables {R : Type} [myfield R]

lemma mul_comm (x y : R) : x * y = y * x := myfield.mul_comm x y
lemma mul_assoc (x y z : R) : (x * y) * z = x * (y * z) := myfield.mul_assoc x y z
lemma mul_one (x : R) : x * 1 = x := myfield.mul_one x
lemma one_mul (x : R) : 1 * x = x := by { rw [mul_comm, mul_one] }
lemma mul_inv (x : R) : x ≠ 0 → x * x⁻¹  = 1 := myfield.mul_inv x
lemma inv_mul (x : R) : x ≠ 0 → x⁻¹ * x = 1 := by {intro h, rw [mul_comm, mul_inv x h], }
lemma mul_add (x y z : R) : x * (y + z) = x * y + x * z := myfield.mul_add x y z
lemma zero_ne_one : (0 : R) ≠ (1 : R) := myfield.zero_ne_one

def mul_identity (u : R) := ∀ x : R, (x * u = x) ∧ (u * x = x)

theorem add_mul (x y z : R) : (x + y) * z = x * z + y * z :=
by { rw [mul_comm, mul_add], repeat { rw mul_comm z _ }, }

theorem mul_identity_unique {a b : R} (h₁ : mul_identity a) (h₂ : mul_identity b)  : a = b :=
by rw [(h₂ a).left.symm, (h₁ b).right]

def mul_inverse (y x : R) := (x * y = 1) ∧ (y * x = 1)

theorem mul_inverse_unique {a b x : R} (h₁ : mul_inverse a x) (h₂ : mul_inverse b x) : a = b :=
by rw [←mul_one a, ←h₂.left, ←mul_assoc, h₁.right, one_mul]

theorem mul_zero {x : R} : x * (0 : R) = (0 : R) :=
begin
  conv {to_rhs, rw ←add_neg' (x*0)},
  conv {to_rhs, congr, rw [←add_zero (0 : R), mul_add], skip},
  rw [add_assoc, add_neg', add_zero],
end

theorem zero_mul {x : R} : (0 : R) * x = (0 : R) := (mul_comm x 0) ▸ mul_zero

theorem neg_one_mul (x : R) : (-1) * x = -x :=
begin
  conv in ((-1)* x) { rw ←(add_zero ((-1)*x)) },
  rw [←(add_neg' x), ←add_assoc],
  conv in ((-1)*x + x) { congr, skip, rw ←(one_mul x) },
  rw [←add_mul, neg_add, zero_mul, zero_add],
end

lemma neg_one_mul_neg_one : (-(1 : R)) * (-1) = 1 :=
by rw [neg_one_mul, neg_neg]

lemma neg_mul_eq_mul_neg (x y : R) : -(x * y) = x * (-y) :=
by rw [←add_zero (x * -y), ←add_neg' (x*y), ←add_assoc, ←mul_add, neg_add, mul_zero, zero_add]

lemma neg_mul_neg_self (x : R) : (-x)*(-x) = x * x :=
by rw [←neg_one_mul, mul_assoc, mul_comm x _, ←mul_assoc, ←mul_assoc, neg_one_mul_neg_one, one_mul]

lemma neg_mul_neg (x y : R) : (-x) * (-y) = x * y :=
begin
  rw [←neg_one_mul, mul_assoc, ←neg_mul_eq_mul_neg, ←neg_one_mul (x*y)], 
  rw [←mul_assoc, neg_one_mul_neg_one, one_mul],
end

lemma one_inv : (1 : R)⁻¹ = (1 : R) :=
by rw [←(mul_one (1 : R)⁻¹), inv_mul (1 : R) (zero_ne_one.symm)]

theorem mul_sub (x y z : R) : x * (y - z) = x * y - x * z :=
begin
  repeat {rw sub_eq_add_neg'},
  rw [mul_add, neg_mul_eq_mul_neg],
end

theorem mul_left_inj' (x a b : R) (h₁ : x ≠ 0): a * x = b * x ↔ a = b :=
⟨λ h, by rw [←(mul_one a), ←(mul_inv x h₁), ←mul_assoc, h, mul_assoc, mul_inv x h₁, mul_one],
λ h, h ▸ rfl ⟩ 

open_locale classical

lemma eq_zero_of_not_eq_zero_of_mul_not_eq_zero (x b : R) (h₁ : b ≠ 0) (h₂ : x * b = 0) : x = 0 :=
begin
  by_cases h : x = 0,
  { exact h },
  { rw [←mul_one x, ←mul_inv x h, mul_comm x x⁻¹, ←mul_one (x * (x⁻¹ * x)), ←mul_inv b h₁],
    rw [mul_assoc, mul_assoc, ←mul_assoc x b _, h₂, zero_mul, mul_zero, mul_zero], }
end

lemma eq_zero_or_eq_zero_of_mul_eq_zero (x y : R) (h : x * y = 0) : x = 0 ∨ y = 0 :=
begin
  by_cases k : y = 0,
  { exact or.inr k },
  { exact or.inl (eq_zero_of_not_eq_zero_of_mul_not_eq_zero x y k h), },
end

lemma mul_inv' (x y : R) (h₁ : x ≠ 0) (h₂ : y ≠ 0) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
begin
  have h : x * y ≠ 0 := λ h, h₁ (eq_zero_of_not_eq_zero_of_mul_not_eq_zero _ _ h₂ h), 
  rw [←(mul_left_inj' _ _ _ h₁), ←(mul_left_inj' _ _ _ h₂)],
  rw [mul_assoc, inv_mul (x * y) h, mul_assoc _ _ x, inv_mul x h₁, mul_one, inv_mul y h₂],
end

theorem inv_ne_zero {a : R} : a ≠ 0 → a⁻¹ ≠ 0 :=
begin
  intros ane0 ainv0,
  have : (1 : R) = (0 : R),
  { rw [←mul_inv a ane0, ainv0, mul_zero], },
  exact zero_ne_one this.symm,
end

theorem inv_inv' (a : R) (h : a ≠ 0 ) : (a⁻¹)⁻¹ = a :=
by rw [←one_mul (a⁻¹)⁻¹, ←mul_inv a h, mul_assoc, mul_inv a⁻¹ (inv_ne_zero h), mul_one]

end fieldlaws

section powers

variables {R : Type} [myfield R]

def pow1 : R → ℕ → R
| x 0            := (1 : R)
| x (nat.succ n) := (pow1 x n) * x  -- `nat.succ` is the Lean version of our function `S`

notation a `^` b := pow1 a b

theorem pow_ne_zero (x : R) (n : ℕ) (h : x ≠ 0) : x ^ n ≠ 0 :=
begin
  induction n with k hk,
  { unfold pow1, exact (zero_ne_one.symm), },
  { unfold pow1, exact λ k, hk (eq_zero_of_not_eq_zero_of_mul_not_eq_zero _ _ h k), },
end

theorem pow1_add (x : R) (m n : ℕ) : x ^ (m + n) = (x ^ m) * (x ^ n) :=
begin
  induction n with k hk,
  { rw nat.add_zero, unfold pow1, rw mul_one, },
  { unfold pow1, rw [hk, ←mul_assoc], },
end

theorem pow1_mul (x : R) (m n : ℕ) : x ^ (m*n) = (x ^ m) ^ n :=
begin
  induction n with k hk,
  { rw nat.mul_zero, unfold pow1, },
  { unfold pow1, rw [nat.succ_eq_add_one, left_distrib, nat.mul_one, pow1_add, hk], },
end

lemma sub_succ_eq_pred_sub_of_le (b k : ℕ) : nat.succ k ≤ b → (b-(nat.succ k)) = (b - 1) - k :=
begin
  induction k with m hm,
  { rw nat.sub_zero, exact λ _, rfl, },
  { exact λ _, (nat.pred_sub b (nat.succ m)).symm, },
end

theorem pow1_sub (x : R) (h₁ : x ≠ 0) (n : ℕ) :
  ∀ m : ℕ, n ≤ m → x ^ (m - n) = (x ^ m) * (x ^ n)⁻¹ :=
begin
  induction n with k hk,
  { intros m h₂,
    rw nat.sub_zero,
    unfold pow1,
    rw [one_inv, mul_one], },
  { unfold pow1,
    intros b h₂,
    rw [mul_inv' _ _ (pow_ne_zero _ _ h₁) h₁, sub_succ_eq_pred_sub_of_le _ _ h₂],
    rw hk (b-1) (nat.pred_le_pred h₂),
    have : b = (nat.succ(nat.pred b)),
    { rw nat.succ_pred_eq_of_pos, 
      exact nat.lt_of_lt_of_le (nat.succ_pos k) h₂, },
    have : x ^ b = x ^ ((b-1) + 1), congr',
    rw [this, pow1_add],
    unfold pow1,
    rw [one_mul, mul_assoc, ←(mul_assoc x _ _ ), (mul_inv x h₁), one_mul], },
end

def pow2 (x : R) (m : ℤ) := ite (m ≥ 0) (x ^ (int.to_nat m)) (x ^ (int.to_nat (-m)))

end powers

end myreal

end mth1001