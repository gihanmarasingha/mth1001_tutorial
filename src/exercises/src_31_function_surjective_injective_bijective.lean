import tactic.linarith
import .src_17_even_odd_further

open function
open int

namespace mth1001 

/-
We define a functions `p₁` and `p₂` so that `p₁ x = x + 3` and  `p₂ x = 2 * x`, 
for every `x : ℤ`.
-/
def p₁ (x : ℤ) : ℤ := x + 3
def p₂ (x : ℤ) : ℤ := 2 * x

#eval p₁ 10 -- `p₁ 10` evaluates to `13`.
#eval p₂ 7  -- `p₂ 7` evaluates to `14`.

section surjective

/-
Let `α` and `β` be types. For a function `f : α → β` to be *surjective* means
`∀ b : β, ∃ a : α, f a = b`
-/
#print surjective

-- We'll show that `p₁` is surjective.
lemma sur_p1 : surjective p₁ :=
begin
  intro b, -- Assume `b : ℤ`. We must show `∃ a, p₁ a = b`.
  unfold p₁, -- By definition of `p₁`, the goal is `∃ a, a + 3 = b`.
  use (b-3), -- By `∃` intro. on `b-3`, it suffices to show `(b-3) + 3 = b`.
  linarith, -- This is true by linear arithmetic.
end

-- We'll show `p₂` is not surjective.
example : ¬(surjective p₂) :=
begin
  unfold surjective, -- By definition, we must show `¬(∀ b, ∃ a, p₂ a = b)`.
  push_neg, -- Pushing in the negation, the goal is `∃ b, ∀ a, p₂ a ≠ b`.
  unfold p₂, -- By defition of `p₂`, this is `∃ b, ∀ a, 2 * a ≠ b`.
  use 1, -- By `∃` intro. on `1`, it suffices to show `∀ a, 2 * a ≠ 1`.
  intros a h, -- For a contradiction, assume `a : ℤ` and `h : 2 * a = 1`.
  -- For the remainder of the proof, we'll get a contradiction by
  -- showing `1` is both odd and not odd.
  have h₂ : odd 1,       -- `h₂ : odd 1` as
  { use 0, norm_num, },  -- `1 = 2 * 0 + 1`.
  have h₃ : even 1,      -- `h₃ : even 1` as
  { use a, rw h, },      -- `1 = 2 * a`, using `h`.
  have h₄ : ¬(odd 1),    -- So `h₄ : ¬(odd 1)` as a number is even iff
  { rw ←even_iff_not_odd, exact h₃, }, -- it is not odd.
  exact h₄ h₂, -- We have `⊥` by false intro. on `h₄` and `h₂`.
end

end surjective

section injective

/-
Let `α` and `β` be types. For a function `f : α → β` to be *injective* means
`∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂`
-/
#print injective

-- We'll show `p₂` is injective.
example : injective p₂ :=
begin
  unfold injective, -- By definions of injective and `p₂`, it suffices to prove
  unfold p₂,        -- `∀ a₁ a₂ : ℤ, 2 * a₁ = 2 * a₂ → a₁ = a₂`.
  intros a₁ a₂ h, -- Assume `a₁ a₂ : ℤ`. Assume `h : 2 * a₁ = 2 * a₂`.
  linarith, -- By linear arithmetic, we have `a₁ = a₂`.
end

-- Now we'll show `p₁` is injective.
lemma inj_p1 : injective p₁ :=
begin
  unfold injective, -- By definions of injective and `p₂`, it suffices to prove
  unfold p₁,        -- `∀ a₁ a₂ : ℤ, a₁ + 3 = a₂ + 3 → a₁ = a₂`.
  intros a₁ a₂ h, -- Assume `a₁ a₂ : ℤ`. Assume `h : a₁ + 3 = a₂ + 3`.
  linarith, -- By linear arithmetic, we have `a₁ = a₂`.
end

end injective

section bijective

-- A function is bijective if it is both injective and surjective.
#print bijective

example : bijective p₁ :=
begin
  unfold bijective, -- It suffices to prove `injective p₁ ∧ sujective p₁`.
  exact and.intro inj_p1 sur_p1, -- This follows by and intro. on `inj_p1` and `sur_p1`.
end

end bijective

end mth1001
