import data.real.basic
import data.set.basic
import tactic

namespace mth1001

/-
We'll only deal with real-valued sequences. Such a sequence is merely a function from `ℕ` to `ℝ`
We'll use the Lean built-in real number type rather than the type we've constructed.
-/

section convergence

-- `convergesto f a` means
def convergesto (f : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (f n - a) < ε

/-
We'll prove that the sequence `f₁ : ℕ → R` given by `f₁(n) = 5` converges to `5`.
-/

def f₁ : ℕ → ℝ := λ n, (5 : ℝ)

example : convergesto f₁ 5 :=
begin
  assume ε : ℝ,
  assume εpos : ε > 0, -- It suffices to prove `∃ N, ∀ n ≥ N, abs (f₁ n - 5) < ε`.
  use 1, -- Take `N := 1`.
  assume n : ℕ,
  assume hn : n ≥ 1,
  unfold f₁, -- By unfolding, it suffices to show `abs (5 - 5) < ε`.
  rw sub_self, -- That is, to prove `abs 0 < ε`.
  rw abs_zero, -- But `abs 0 = 0`, so it suffices to prove `0 < ε`.
  exact εpos, -- This holds by `εpos`.
end

/-
More generally, we'll show a constant sequence converges.
-/

-- Exercise 219:
lemma convergesto_const (c : ℝ) : convergesto (λ n, c) c :=
begin
  assume ε : ℝ,
  assume εpos : ε > 0,
  sorry  
end

end convergence

section uniqueness_of_limits

variables {f : ℕ → ℝ} {a b : ℝ}

-- We proved the following result earlier for our own real number type.
lemma zero_of_non_neg_of_lt_pos' {a : ℝ} (h : 0 ≤ a) (h₂ : ∀ ε > 0, a < ε) : a = 0 :=
begin
  apply eq_of_le_of_forall_le_of_dense h,
  intros ε εpos,
  specialize h₂ ε εpos,
  exact le_of_lt h₂,
end

-- We'll need the following results for the proof of the next lemma.
example (x y : ℝ) : abs (x + y) ≤ abs x + abs y := abs_add x y
example (x : ℝ) : abs (-x) = abs x := abs_neg x
example (a b c : ℝ) (h : a < b) : a + c < b + c := add_lt_add_right h c
example (a b c : ℝ) (h : a < b) : c + a < c + b := add_lt_add_left h c

-- Exercise 220:
lemma convergesto_unique (h₁ : convergesto f a) (h₂ : convergesto f b) : a = b :=
begin
  suffices h : abs (a - b) = 0,
  { rwa [←sub_eq_zero, ←abs_eq_zero] },
  have k₁ : abs (a - b) ≥ 0, from abs_nonneg (a - b),
  suffices h : ∀ ε > 0, abs (a - b) < ε, from zero_of_non_neg_of_lt_pos' k₁ h,
  sorry  
end

end uniqueness_of_limits

section algebra_of_limits

variables (f g : ℕ → ℝ) -- `f` and `g` are sequences
variables (a b c : ℝ)

-- The following result will often come in handy!
lemma div_abs_pos_of_pos_of_non_zero {ε c : ℝ} (εpos : ε > 0) (h : c ≠ 0) : ε / abs c > 0 :=
begin
  have h₂ : 0 < abs c, from  abs_pos_iff.mpr h,
  have h₃ : 0 < (abs c)⁻¹, from inv_pos.mpr h₂,
  exact mul_pos εpos h₃,
end

example (a b c : ℝ) (h₁ : a < b / c) (h₂ : 0 < c): a * c < b := (lt_div_iff h₂).mp h₁

example (a b : ℝ) : abs (a*b) = abs a * abs b := abs_mul a b

example (x y : ℝ) : x ≤ max x y := le_max_left x y

example (x y : ℝ) : y ≤ max x y := le_max_right x y

theorem convergesto_scalar_mul (h : convergesto f a) : convergesto (λ n, c * (f n)) (c * a) :=
begin
  by_cases h₂ : c = 0,
  { simp only [h₂, zero_mul], -- `simp` is a simiplying tactic.
    exact convergesto_const 0, },
  { assume ε : ℝ,
    assume εpos : ε > 0,
    have h₃ : ε / abs c > 0, from div_abs_pos_of_pos_of_non_zero εpos h₂,
    cases h (ε/ abs c) h₃ with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    have h₄ : abs c > 0, from abs_pos_iff.mpr h₂,
    have h₅ : abs (f n -a) * abs c < ε, from (lt_div_iff h₄).mp hN,
    have h₆ : abs ((f n - a)* c) < ε, { rwa abs_mul, },
    rwa [←mul_sub, mul_comm], },
end

theorem convergesto_add (h₁ : convergesto f a) (h₂ : convergesto g b )
: convergesto (λ n, f n + g n) (a + b) :=
begin
  assume ε : ℝ,
  assume εpos : ε > 0,
  cases h₁ (ε/2) (by linarith) with N₁ hN₁,
  cases h₂ (ε/2) (by linarith) with N₂ hN₂,
  use (max N₁ N₂),
  intros n hn,
  have k₁ : n ≥ N₁, from le_trans (le_max_left N₁ N₂) hn,
  have k₂ : n ≥ N₂, from le_trans (le_max_right N₁ N₂) hn,
  have m₁ : abs (f n - a) < ε/2, from hN₁ n k₁,
  have m₂ : abs (g n - b) < ε/2, from hN₂ n k₂,
  have h₃ : (f n + g n) - (a + b) = (f n - a) + (g n - b), ring,
  rw h₃,
  calc abs (f n - a + (g n - b))
        ≤ abs (f n - a) + abs (g n - b) : abs_add _ _
    ... < ε/2 + ε/2                     : by linarith
    ... = ε                             : by linarith,
end

-- The same proof can be written more briefly using `congr'` and by giving arguments to `linarith`.
example (h₁ : convergesto f a) (h₂ : convergesto g b ) : convergesto (λ n, f n + g n) (a + b) :=
begin
  intros ε εpos,
  cases h₁ (ε/2) (by linarith) with N₁ hN₁,
  cases h₂ (ε/2) (by linarith) with N₂ hN₂,
  use (max N₁ N₂),
  intros n hn,
  have k₁ : n ≥ N₁, from le_trans (le_max_left N₁ N₂) hn,
  have k₂ : n ≥ N₂, from le_trans (le_max_right N₁ N₂) hn,
  calc abs ((f n + g n) - (a + b))
        = abs (f n - a + (g n - b))     : by {congr', ring}
    ... ≤ abs (f n - a) + abs (g n - b) : abs_add _ _
    ... < ε/2 + ε/2                     : by linarith [hN₁ n k₁, hN₂ n k₂]
    ... = ε                             : by linarith,
end

end algebra_of_limits

section specific_example

/-
In Lean, it's often harder to work with particular examples than with general theorems.
Here, we show convergence of a particular sequence.

We'll need the corollorary to the Archimedean property. In Lean,this is `exists_nat_one_div_lt`.
Note the use of `↑n` to indicate the embedding (or coercion) of the natural number `n`
as a real number.
-/

example (ε : ℝ) (h : 0 < ε) : ∃ n : ℕ, 1/(↑n + 1) < ε := exists_nat_one_div_lt h

example (x : ℝ) (h : x > 0) : abs x = x := abs_of_pos h

example (x : ℝ) (h : 0 < x) : 0 < x⁻¹ := by {rwa inv_pos}

example (x : ℝ) (h : 0 < x) : x⁻¹ = (1 : ℝ) / x := inv_eq_one_div x

-- Now we'll show the sequence given by `λ n, 3 + 1/n` converges to `3`.
example : convergesto (λ n, 3 + 1/n) 3 :=
begin
  unfold convergesto,
  assume ε εpos,
  have h : ∃ N : ℕ, 1/(↑N + 1) < ε, from exists_nat_one_div_lt εpos,
  cases h with N hN, -- By `∃` elim. on `h`, STP the goal assuming `N : ℕ` and `hN : 1/(↑N+1) < ε`.
  use N + 1, -- By `∃` intro on `N + 1`, it suffices to prove
  -- `∀ n ≥ N + 1, n ≥ N + 1 → abs (3 + 1/↑n - 3) < ε`.
  assume n hn, -- assume `n : ℕ` and `hn : n ≥ N`.
  have h₂ : abs ((3 : ℝ) + 1 / ↑n - 3)  = abs (↑n)⁻¹, ring,
  rw h₂,
  have : N + 1 > 0, linarith,
  have : n > 0, linarith,
  have :  (0 : ℝ) < ↑n, { rwa nat.cast_pos },
  have : (0 : ℝ) < N + 1, {change (0 : ℝ) < ↑(N + 1), rw nat.cast_pos, linarith, },
  have : (0 : ℝ) < (↑n)⁻¹, { rwa inv_pos },
  rw abs_of_pos this,
  have : (↑n)⁻¹ ≤ (↑N + (1 : ℝ))⁻¹,
  { rw inv_le_inv, 
    change ↑(N + 1) ≤ ↑n,
    rwa nat.cast_le,
    repeat { assumption }, },
  apply lt_of_le_of_lt,
  { assumption, },
  { rwa inv_eq_one_div, },
end

end specific_example

end mth1001
