import data.set.function
import tactic.linarith

import tactic.norm_num

open function

namespace mth1001

section identity

/-
For a given type `α`, there is a special function, the identity function `id : α → α` defined so
that `id a = a`, for every `a : α`.
-/

def p₁ (x : ℕ) : ℤ := 3 * x

/-
For every function `f : α → β`, we have `id ∘ f = f` and `f ∘ id = f`.
-/
#eval (p₁ ∘ id) 6
#eval (id ∘ p₁) 6

/-
To be more precise, we should acknowledge that the identity function `id : α → α` depends on the
type `α`. In Lean, we dentote this function by `@id α`. In mathematical writing, we may use a
subscript `id_α` instead.

So if `f : α → β`, then `f ∘ @id α = f` and `@id β ∘ f = f`.
-/

#check p₁ ∘ @id ℕ
#check @id ℤ ∘ p₁

end identity

section inverse_examples

/-
Given a function `f : α → β`, a function `g : β → α` is a *right inverse* of `f` if
`∀ b : β, f (g b) = b`. The function `h : β → α` is a *left inverse* of `f` if
`∀ a : α, h (f a) = a`. The notions are captured by the Lean defintions `right_inverse` and
`left_inverse`.

An equivalent characterisation:

Given a function `f : α → β`, a function `g : β → α` is a *right inverse* of `f` if `f ∘ g = @id β`.
A function `h : β → α` is a *left inverse* of `f` if `h ∘ f = @id α`.

Given `k₁ : left_inverse h f`, i.e. that `h` is a left inverse of `f` &
given `k₂ : right_inverse g f`, i.e. that `g` is a right inverse of `f`,
`left_inverse.comp_eq_id k₁` is a proof that `h ∘ f = id` and
`right_inverse.comp_eq_id k₂` is a proof that `f ∘ g = id`.

Note: if `g` is a right inverse of `f`, then `f` is a left inverse of `g`, and vice versa.
-/
#print left_inverse
#print right_inverse


-- We'll construct a left inverse of the function `f₁ : ℕ → ℤ`, `f₁ x = x + 3`.
def f₁ (x : ℕ) : ℤ := x + 3

/-
The function `φ₁` below is defined piecewise.
-/
def φ₁ : ℤ → ℕ
| (n + 3 : ℕ) := n -- If `x ≥ -3`, then `φ₁ x = x - 3`.
| _ := 0           -- Otherwise, `φ₁ x = 0`.

#eval φ₁ 2 -- `φ₁ 2 = 0`
#eval φ₁ 8 -- `φ₁ 8 = 8 - 3 = 5`.

-- We show `φ₁` is a left inverse of `f₁` (equally, `f₁` is a right inverse of `φ₁`).
lemma left_inv_phi1f1: left_inverse φ₁ f₁ :=
begin
  intro x, -- Assume `x : ℕ`. It suffices to prove `φ₁ (f₁ x) = x`.
  split, -- This holds for each of the cases that define `φ₁`.
end

/-
Here's another piecewise function.
-/
def φ₂ : ℤ → ℕ
| (n + 3 : ℕ) := n -- If `x ≥ 3`, then `φ₂ x = x - 3`.
| _ := 720           -- Otherwise, `φ₂ x = 720`.

#eval φ₂ 2 -- `φ₂ 2 = 720`
#eval φ₂ 8 -- `φ₂ 8 = 8 - 3 = 5`.

-- We show `φ₂` is also a left inverse of `f₁` (equally, `f₁` is a right inverse of `φ₂`).
lemma left_inv_phi2f1 : left_inverse φ₂ f₁  :=
begin
  intro x, -- Assume `x : ℕ`. It suffices to prove `φ₂ (f₁ x) = x`.
  split, -- This holds for each of the cases that define `φ₂`.
end

/-
The upshot of these two examples is that even when a function has a left inverse, that left inverse
need not be *unique*. Here, both `φ₁` and `φ₂` are left inverses of `f₁`.
-/

/-
As noted, `f₁` is a right inverse of `φ₁`. We'll now find *another* right inverse of `φ₁`.
-/
def f₂ : ℕ → ℤ
| 0 := 2        -- `f₂ 0 = 2`. For other values, `n`, of the input,
| n := n + 3    -- `f₂ n = n + 3`.

example : right_inverse f₂ φ₁ :=
begin
  intro x, -- Assume `x : ℕ`. It suffices to prove `φ₁ (f₂ x) = x`.
  by_cases h : (x = 0), -- We consider two cases 1. `h : x = 0` and 2. `h : x ≠ 0`.
  { rw h, -- Substituting `h : x = 0`, the goal is `φ₁ (f₂ 0) = 0`.
    refl, }, -- This is true, by reflexivity.
  { rw f₂,   -- Use the definition of `f₂`.
    { split, },     -- Consider all
    { exact h, },}, -- possible cases.
end

end inverse_examples

section uniqueness_theorems

variable {α : Type*}
variable {β : Type*}

-- A function that has both a left and a right inverse is said to be *invertible*.
def invertible (f : α → β) := has_left_inverse f ∧ has_right_inverse f

-- For example, the identity function on any type is invertible.
example : invertible (@id α) :=
begin 
  split, -- It suffices to prove `has_left_inverse (@id α)` and `has_right_inverse (@id α)`.
  { use (@id α), -- It suffices to show `@id α` is a left inverse of `@id α`.
    intro x, -- Assume `x : α`. It suffices to prove `id (id x) = x`.
    unfold id, }, -- This follows by definition of `id`.
  { use (@id α), -- It suffces to show `@id α` is a right inverse of `@id α`.
    intro x, -- Assume `x : α`. It suffices to prove `id (id x) = x`.
    unfold id, }, -- This follos by definition of `id`.
end

/-
Inverses are unique in the following sense. If a function `f : α → β` has a left inverse
`h : β → α` and a right inverse `g : β → α`, then `h = g`.

The proof below uses *functional extensionality*. This is the principle that, given functions
`h : β → α` and `g : β → α`, the claim `h = g` is equivalent to the claim `∀ b : β, h b = g b`.
-/
theorem left_inverse_eq_right_inverse (f : α → β) (g h : β → α) (k₁ : left_inverse h f)
  (k₂ : right_inverse g f) : h = g :=
begin
  ext b, -- Assume `b : β`. It suffices to prove `h b = g b`.
  calc h b = h (f (g b)) : by rw k₂ b  -- Note `f (g b) = b`, as `g` is a right inverse of `f`.
       ... = g b         : k₁ (g b) -- Further, `h (f (g b)) = g b`, as `h` is left inverse of `f`.
end

/-
The result can also be proved using the composite-based definition of left and right inverses.
The proof below, though longer, is illustrative of more general principles in algebra that you
will see next term and in later years.
-/
example  (f : α → β) (g h : β → α) (k₁ : left_inverse h f)
  (k₂ : right_inverse g f) : h = g :=
begin
  calc  h = h ∘ id        : rfl  -- This holds by reflexivity
      ... = h ∘ (f ∘ g)   : by rw (right_inverse.comp_eq_id k₂)
      ... = (h ∘ f) ∘ g   : rfl 
      ... = id ∘ g        : by rw (left_inverse.comp_eq_id k₁)
      ... = g             : rfl 
end

/-
As a simple corrolary, every invertible function has exactly one left inverse and exactly one right
inverse. 
-/
theorem unique_left_inverse_of_invertible (f : α → β) (fi : invertible f) (h₁ h₂ : β → α)
  (k₁ : left_inverse h₁ f) (k₂ : left_inverse h₂ f) : h₁ = h₂ :=
begin
  sorry  
end

theorem unique_right_inverse_of_invertible (f : α → β) (fi : invertible f) (g₁ g₂ : β → α)
  (k₁ : right_inverse g₁ f) (k₂ : right_inverse g₂ f) : g₁ = g₂ :=
begin
  sorry  
end

/-
The function `f₁ : ℕ → ℤ` defined before by `f x := x + 3` has (at least) two different left
inverses, `φ₁` and `φ₂`. We infer that `f₁` cannot be invertible!
-/

end uniqueness_theorems

section inverse_theorems

variable {α : Type*}
variable {β : Type*}

/-
We'll show that a function is surjective if it has a right inverse.
-/
theorem surjective_of_right_inverse (f : α → β) (g : β → α) (h : right_inverse g f) :
  surjective f :=
begin
  sorry  
end

/-
Now we'll show a function is injective if it has a left inverse. We'll give two proofs.
The second is nicer but it introduces some new Lean syntax.
-/
example (f : α → β) (g : β → α) (h : left_inverse g f) : injective f :=
begin
  intros a₁ a₂ h₂, -- Assume `a₁ a₂ : α` and `h₂ : f a₁ = f a₂`.
  have h₃ : g (f a₁) = g (f a₂),
  { rw h₂, },
  have h₄ : a₁ = g (f a₁), from (h a₁).symm,
  have h₅ : g (f a₂) = a₂, from h a₂,
  transitivity,
  { exact h₄, },
  { transitivity,
    { exact h₃, },
    { exact h₅, }, }, 
end

/-
The proof above used two applications of transitivity on three new hypotheses.
Calculations like this can be expressed in `calc` mode, which simulates a
mathematical series of calculations.
-/
theorem injective_of_left_inverse (f : α → β) (g : β → α) (h : left_inverse g f) : injective f :=
begin
  intros a₁ a₂ h₂, -- Assume `a₁ a₂ : α` and `h₂ : f a₁ = f a₂`.
  calc a₁ = g (f a₁) : (h a₁).symm
      ... = g (f a₂) : by rw h₂
      ... = a₂       : h a₂
end

/-
Combining the results above, we see that every invertible function is bijective.
-/

theorem bijective_of_invertible (f : α → β) (k : invertible f) : bijective f :=
begin
  sorry    
end

end inverse_theorems

section application_of_inverse_theorems

/-
Earlier, we showed that the function `f₁ : ℕ → ℤ` given by `f₁ x = x + 3` has a left inverse
(indeed, it has more than one left inverse).  We infer that `f₁` is injective.
-/
example : injective f₁ :=
injective_of_left_inverse f₁ φ₁ left_inv_phi1f1

/-
It wasn't clear at the time whether `f₁` has a right inverse.
We'll now show that `f₁` *doesn't* have a right inverse. We do this by using the contrapositive
of the result that a function with a right inverse is surjective.
-/
example : ¬(has_right_inverse f₁) :=
begin
  intro h,
  have h₂ : surjective f₁, from surjective_of_has_right_inverse h,
  have h₃ : ¬(∃ x : ℕ, f₁ x = -1), -- We have `h₃`: there is no `x : ℕ` for which `f₁ x = -1`.
  { push_neg,                      -- Don't be too concerned about the details
    intro x,                       -- of the proof of `h₃`.
    unfold f₁,
    have : ↑x + (3 : ℤ) ≥ 0,
    { norm_num, },
    linarith, },
  specialize h₂ (-1 : ℤ), -- By surjectivity of `f₁`, `∃ a : ℕ, f₁ a = -1`.
  exact h₃ h₂, -- But this contradicts `h₃`.
end

/-
Likewise, we'll show that `φ₁` is surjective, but does not have a left inverse.
N.B. `left_inv_phi1f1` below is equivalent to the assertion that `f₁` is a right inverse of `φ₁`.
-/

example : surjective φ₁ :=
surjective_of_right_inverse φ₁ f₁ left_inv_phi1f1

example : ¬(has_left_inverse φ₁) :=
begin
  intro h,
  have h₂ : injective φ₁, from injective_of_has_left_inverse h,
  unfold injective at h₂,
  have h₃ : φ₁ 0 = φ₁ 1,
  { split, },
  have h₄ : (0 : ℤ) = 1, from h₂ h₃,
  linarith,
end

end application_of_inverse_theorems

end mth1001
