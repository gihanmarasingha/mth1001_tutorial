import data.finset
import algebra.big_operators
import tactic.ring
import tactic.linarith

namespace mth1001


open_locale big_operators
open finset nat

section induction

/-
Here, the symbol `ℕ`, written `\N` represents the non-negative integers. 
Take care: some mathematicans use `ℕ` to represent the postive integers.
-/

/-
In the following definition, `range n` is, for `n > 0`, the set of `n` integers `{0, 1, …, n}`. In
the special case `n = 0`, the quantity `range 0` is the empty set.

The summation symbol `∑` is written `\sum`.
-/

/-
`powers_of_two_sum n` is the sum `1 + 2^1 + 2^2 + ⋯ + 2^(n-1)`, if `n > 0`. If `n=0`, then we are
summing over the empty set. By defintion, any sum over the empty set is `0`.
-/
def powers_of_two_sum (n : ℕ)  := ∑ i in range n, 2^i

#eval powers_of_two_sum 10
#eval powers_of_two_sum 0


/-
We'll prove that `powers_of_two_sum n` is `2^n - 1`, for every non-negative integer `n`.
-/

lemma one_le_two_pow (n : ℕ) : 1 ≤ 2^n :=
calc 1  = 1^n : (nat.one_pow n).symm
    ... ≤ 2^n : nat.pow_le_pow_of_le_left dec_trivial n

example (n : ℕ) : powers_of_two_sum n = 2^n - 1:=
begin 
  induction n with k h_ih,
  { exact sum_empty, },
  { unfold powers_of_two_sum at *,
    rw sum_range_succ,
    rw h_ih,
    rw nat.pow_succ,
    calc 2^k + (2^k - 1) = (2^k + 2^k) -1 : (nat.add_sub_assoc (one_le_two_pow k) _).symm
                     ... =  2^k * 2 - 1   : by rw mul_two },
end 

def triangle_sum (n : ℕ) := ∑ i in range (n + 1), i

#eval triangle_sum 10

example (n : ℕ) : 2 * triangle_sum n = n * (n+1) :=
begin 
  induction n with k h_ih,
  { unfold triangle_sum,
    rw sum_range_one,
    norm_num, },
  { unfold triangle_sum at *,
    rw sum_range_succ,
    rw mul_add,
    rw h_ih,
    rw succ_eq_add_one,
    ring, },
end 

lemma sub_lt_of_gt {k c : ℕ} (h₁ : k > c) (h₂ : c > 0): k - c < k :=
begin 
  apply nat.sub_lt,
  linarith,
  linarith,
end

example (n : ℕ) : n ≥ 4 → (∃ s t : ℕ, n = 5 * s + 2 * t) :=
begin 
  apply nat.strong_induction_on n,
  intros k h hk,
  by_cases h₁ : k > 5,
  { specialize h (k-2),
    have h₂ : k - 2 < k,
    { apply sub_lt_of_gt,
      repeat { linarith }, },
    have h₃ : k - 2 ≥ 4,
    { exact nat.le_sub_left_of_add_le h₁ },
    cases h h₂ h₃ with a ha,
    cases ha with b hb,
    use [a,b+1],
    have h₄ : k - 2 + 2 = k := nat.sub_add_cancel (by linarith),
    have h₅ : k = (5 * a + 2 * b) + 2,
    { rw [←h₄, hb], },
    linarith, },
  { by_cases h₂ : k = 4,
    { rw h₂,
      use [0,2],
      norm_num, },
    { have h₃ : k > 4 := lt_of_le_of_ne hk (ne.symm h₂),
      have h₄ : k = 5 := le_antisymm (by linarith) h₃,
      rw h₄,
      use [1,0],
      norm_num, }, },
end 

end induction 

end mth1001
