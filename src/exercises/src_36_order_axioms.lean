import ..library.src_ordered_field

namespace mth1001

namespace myreal

section ordered

variables {R : Type} [myordered_field R]

open_locale classical

open myordered_field

/-
The three basic axiom of an orderd field are:

1. `trichotomy`,
2. `pos_add_of_pos_of_pos`, and
3. `pos_mul_of_pos_of_pos`,

as exemplified below
-/

example (x : R) : pos x ∧ ¬x = 0 ∧ ¬pos (-x)
               ∨ ¬pos x ∧ x = 0  ∧ ¬pos (-x)
               ∨ ¬pos x ∧ x ≠ 0 ∧ pos (-x) := trichotomy x

example (x y : R) : pos x → pos y → pos (x + y) := pos_add_of_pos_of_pos x y

example (x y : R) : pos x → pos y → pos (x * y) := pos_mul_of_pos_of_pos x y

-- In the example below, we see that the square of non-zero positive number is positive.
example (x : R) (h : x ≠ (0 : R)) : pos (pow1 x 2) :=
begin
  unfold pow1, -- Use the definition of exponentiation.
  rcases trichotomy x with ⟨hpx, _, _⟩ | ⟨_, rfl, _⟩ | ⟨_, _, hpnx⟩,
  { rw one_mul, exact pos_mul_of_pos_of_pos _ _ hpx hpx, },
  { rw mul_zero, contradiction, },
  { rw [one_mul, ←neg_mul_neg_self],
    exact pos_mul_of_pos_of_pos _ _ hpnx hpnx,},
end

-- Exercise 177:
-- Use trichotomy on `(1 : R)`, as in the example above.
lemma pos_one : pos (1 : R) :=
begin
  sorry  
end

-- Below, we see that every non-zero natural number (seen as a term of type `R`) is positive.
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

-- The lemmas below are used to work with the definition of `<`.

lemma lt_iff_pos_sub (x y : R) : x < y ↔ pos (y -x) := by refl

lemma lt_iff_pos_neg (x y : R) : x < y ↔ pos (y + -x) := by refl

-- Exercise 178:
lemma gt_zero_mul_of_gt_zero_of_gt_zero {a b : R} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b :=
begin
  sorry  
end

-- Exercise 179:
lemma neg_pos {x : R} : 0 < -x ↔ x < 0:=
begin
  repeat {rw lt_iff_pos_neg},
  sorry  end

-- Exercise 180:
lemma trichotomy' (x y: R) : x < y ∧ ¬x = y ∧ ¬y < x ∨
                               ¬x < y ∧ x = y ∧ ¬y < x ∨
                               ¬x < y ∧ ¬x = y ∧ y < x :=
begin
  repeat {rw lt_iff_pos_sub},
  have : x - y = -(y - x),
  { sorry, }, 
  sorry  
end

-- Exercise 181:
lemma lt_trans {x y z : R} : x < y → y < z → x < z :=
begin
  repeat {rw lt_iff_pos_sub},
  sorry  
end

-- Exercise 182:
lemma add_lt_add_iff_right_mpr {x y : R} (z : R) : x < y → x + z < y + z :=
begin
  sorry  
end

-- Exercise 183:
lemma add_lt_add_iff_right_mp {x y : R} (z : R) : x + z < y + z → x < y :=
begin
  sorry  
end

-- Exercise 184:
lemma add_lt_add_iff_right {x y : R} (z : R) : x + z < y + z ↔ x < y :=
begin
  sorry  
end

-- Exercise 185:
theorem neg_lt_neg_iff  {a b : R} : -a < -b ↔ b < a :=
begin
  sorry  
end

-- Exercise 186:
lemma mul_lt_mul_left_mpr {x y z : R} : 0 < z → x < y → z * x < z * y :=
begin
  sorry  
end

-- Exercise 187:
theorem add_lt_add {a b c d : R} : a < b → c < d → a + c < b + d :=
begin
  sorry  
end

-- Exercise 188:
lemma lt_irrefl {x : R} : ¬x < x :=
begin
  sorry  
end

-- Exercise 189:
-- Use `lt_irrefl` to prove the following.
theorem ne_of_gt {a b : R} (h : a > b) : a ≠ b :=
begin
  sorry  end

-- The following lemma is used to work with the definition of `≤`.

lemma le_iff_lt_or_eq {x y : R} : x ≤ y ↔ ((x < y) ∨ x = y) := by refl

-- Exercise 190:
lemma le_refl (x : R) : x ≤ x :=
sorry 

-- Exercise 191:
-- Though it looks complicated, you can fill in the `sorry` below using only the
-- `split`, `intro`, and `exact` tactics (with and introduction and hypotheses).
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
  { sorry, }, 
end

-- Exercise 192:
-- Use `neg_le_iff_lt` to prove the result below.
lemma not_lt_iff_le (x y : R) : ¬(x < y) ↔ (y ≤ x) :=
sorry 

-- Exercise 193:
lemma neg_nonneg {x : R} : 0 ≤ -x ↔ x ≤ 0 :=
begin
  repeat {rw le_iff_lt_or_eq},
  have k : 0 < -x ↔ x < 0, from neg_pos,
  sorry  
end


-- Exercise 194:
lemma le_trans (x y z : R) : x ≤ y → y ≤ z → x ≤ z :=
begin
  rintro (h₁ | rfl) (h₂ | rfl),
  { sorry, }, 
  { sorry, }, 
  { sorry, }, 
  { sorry, }, 
end

-- Exercise 195:
lemma lt_of_le_of_lt {a b c : R} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
begin
  sorry    
end

-- Exercise 196:
-- Use `rcases trichotomy' x y` (see examples above) to prove the following.
lemma le_total (x y : R) : x ≤ y ∨ y ≤ x :=
begin
  sorry  
end


-- Exercise 197:
lemma anti_symm {x y : R} : x ≤ y → y ≤ x → x = y :=
begin
  sorry  
end

-- Exercise 198:
theorem neg_le_neg_iff {a b : R} : -a ≤ -b ↔ b ≤ a :=
begin
  repeat {rw le_iff_lt_or_eq},
  split,
  { rintro (hlt | heq),
    { left, rwa ←neg_lt_neg_iff, },
    { right, rw [←neg_neg a, heq, neg_neg], }, },
  { sorry, }, 
end

-- Exercise 199:
theorem add_le_add {a b c d : R} : a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  sorry  
end

-- Exercise 200:
theorem mul_self_non_neg (a : R) : 0 ≤ a * a:=
begin
  rcases trichotomy' 0 a with ⟨posa, _⟩ | ⟨_, eq0, _⟩ | ⟨_, _, nega⟩,
  { sorry, }, 
  { sorry, }, 
  { sorry, }, 
end

-- Exercise 201:
lemma non_neg_mul_of_non_neg_of_non_neg {a b : R} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b :=
begin
  cases h₁ with apos aeq0,
  { cases h₂ with bpos beq0,
    { sorry, },  
    { right, rw [←beq0, mul_zero], }, },
  { sorry, }, 
end

-- Exercise 202:
lemma non_neg_of_non_neg_mul_of_pos {x y : R} (h₁ : 0 ≤ x * y) (h₂ : 0 < x) : 0 ≤ y :=
begin
  sorry  
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

-- Exercise 203:
-- Modify the proof of the second case to prove the first case.
theorem inv_pos {a : R}  (h : a ≠ 0) : 0 < a⁻¹ ↔ 0 < a :=
begin
  split,
  { sorry, }, 
  { intro k,
    have h₂ : 0 ≤ (a⁻¹ * a⁻¹), from mul_self_non_neg a⁻¹,
    rw le_iff_lt_or_eq at h₂,
    cases h₂ with posainvsq eq0,
    { convert mul_lt_mul_left_mpr k posainvsq,
      { rw mul_zero, },
      { rw [←mul_assoc, mul_inv a h, one_mul], }, },
    { have h₃ : a⁻¹ = 0,
      { cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ eq0.symm;
        assumption, },
      exact absurd h₃ (inv_ne_zero h), }, },
end

-- Exercise 204:
theorem inv_lt_inv {a b : R} (h₁ : 0  < a) (h₂ : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
begin
  split,
  { sorry, }, 
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

/-
The absolute value `abs a` of `a : R` is defined to be by maximum of
`a` and `-a`.
-/

example (a : R) : abs a = max a (-a) := rfl

/-
By definition, `max a b` is `a` if `b ≤ a`, otherwise it is `b`.

Note the use of `if_pos` and `if_neg` below to distiguish between the cases where
`b ≤ a` and `¬(b ≤ a)` in the definition of `max`.
-/

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

-- Exercise 205:
lemma le_max_right (a b : R) : b ≤ max a b :=
begin
  unfold max,
  by_cases h : b ≤ a,
  { rw (if_pos h),
    sorry, }, 
  { rw (if_neg h),
    sorry, }, 
end

-- Exercise 206:
-- Prove this using the template of the above two results.
lemma max_choice (a b : R) : max a b = a ∨ max a b = b :=
begin
  sorry  
end

lemma neg_le_abs (a : R) : -a ≤ abs a :=
begin
  unfold abs max,
  by_cases h : -a ≤ a,
  { rw (if_pos h), exact h, },
  { rw (if_neg h), exact le_refl (-a), },
end

-- Exercise 207:
lemma le_abs_self (a : R) : a ≤ abs a :=
begin
  sorry  
end

-- Exercise 208:
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
  { sorry, }, 
end

end max_abs

section upper_bounds_lower_bounds_sup

open myordered_field

variables {R : Type} [myordered_field R]

/-
Here are archetypal applications of the definitions of `upper_bound`, `lower_bound`,
`bounded_above`, `bounded_below`, `bounded`, and `is_sup`.
-/

example (u : R) (S : set R) (h : ∀ s ∈ S, s ≤ u) : upper_bound u S := h
example (v : R) (S : set R) (h : ∀ s ∈ S, v ≤ s) : lower_bound v S := h
example (S : set R) (h : ∃ u : R, upper_bound u S) : bounded_above S := h
example (S : set R) (h : ∃ v : R, lower_bound v S) : bounded_below S := h
example (S : set R) (h₁ : bounded_above S) (h₂ : bounded_below S) : bounded S := and.intro h₁ h₂
example (u : R) (S : set R) (h₁ : upper_bound u S) (h₂ : ∀ v : R, upper_bound v S → u ≤ v)
: is_sup u S := and.intro h₁ h₂

-- Exercise 209:
theorem sup_uniqueness (S : set R) (a b : R) (h₁ : is_sup a S) (h₂ : is_sup b S) : a = b :=
begin
  cases h₁ with h₃ h₄,
  cases h₂ with h₅ h₆,
  apply anti_symm,
  { sorry, }, 
  { sorry, }, 
end

-- Exercise 210:
-- In this example, we show _every_ real number `u` is an upper bound of the empty set.
theorem empty_set_upper_bound (u : R) : upper_bound u ∅ :=
begin
  sorry    
end

-- Exercise 211:
theorem empty_set_lower_bound (v : R) : lower_bound v ∅ :=
begin
  sorry  
end

-- Exercise 212:
-- Given `S` a set of real numbers, given `s ∈ S`, given `u` and `v` are upper and lower bounds
-- of `S`, respectively, then `v ≤ u`.
example (S : set R) (u v : R) (h₁ : upper_bound u S) (h₂ : lower_bound v S) (s : R) (h₃ : s ∈ S)
  : v ≤ u :=
begin
  sorry  
end

-- Exercise 213:
-- However, it's *not true* that for every set `S` of real numbers, for all real numbers `u` and `v`,
-- if `u` and `v` are upper and lower bounds of `S`, respectively, then `v ≤ u`.
-- Hint: start with `push_neg` and think of the results above.
example : ¬(∀ (S : set R), ∀ u v : R, upper_bound u S → lower_bound v S → v ≤ u) :=
begin
  sorry  
end

end upper_bounds_lower_bounds_sup

end myreal

end mth1001
