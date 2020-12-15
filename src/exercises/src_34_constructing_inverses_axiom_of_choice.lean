import data.set.function
import .src_33_identity_and_inverse_functions

import tactic.norm_num

open function

namespace mth1001

/-
What about the 'converses' of these statements? Asserting the converses requires classical
reasoning and a principle called the *axiom of choice*.

Further, we'll use predicates `has_left_inverse` and `has_right_inverse`, which are merely
existentially quantified statements concerning left and right inverses.
-/

#print has_left_inverse
#print has_right_inverse

open classical

section aoc
/-
The axiom of choice is best explained via an example. Let `U` denote the type of all modules
currently running at Exeter and let `V` denote the type of all students at Exeter.

For `u : U` and `v : V`, we denote by `R u v` the notion that student `v` is enrolled on module `u`.
[Here, `R : U → V → Prop` is a predicate on the types `U` and `V`. A predicate on more than one
type is sometimes referred to as a *relation*. So `R` is a relation on `U` and `V`.]

We have `h : ∀ u : U, ∃ v : V, R u v`. That is, for every module `u`, there is a student `v` who is
enrolled on `u`.

The axiom of choice asserts, under these hypotheses, that there is a function `g : U → V` such that`
`R u (g u)` holds, for every `u : U`.

In our example, this means that for every module `u`, `g(u)` is a student enrolled on `u`.
In other words, the axiom of choice guarantees the existence of a function that has *chosen*, for
each module `u`, a student `v` enrolled on `u`. Clearly, this function is not unique! There are 
many functions with this property, but we need the axiom of choice to ensure the *existence* of
such a function.
-/


  variable U : Type*
  variable V : Type*
  variable R : U → V → Prop

  example (h : ∀ u : U, ∃ v : V, R u v) : ∃ g : U → V, ∀ u : U, R u (g u) :=
  axiom_of_choice h

end aoc

section constructing_inverses

variable {α : Type*}
variable {β : Type*}

/-
The axiom of choice gives a 'one-line' proof that a surjective function has a right inverse.
If you place your cursor after the last `unfold` below, you'll see that `h` asserts
`h : ∀ b : β, ∃ a : α, f a = b`.

In our expression of the axiom of choice, `β` takes the role of `U`, `α` the role of `V`, and
`f a = b` the role of `R b a`. The axiom of choice thus asserts the existence of `g : β → α`
such that `∀ β : β, f (g b) = b`. That is, `g` is a right inverse of `g`.
-/
theorem has_right_inverse_of_surjective {f : α → β} (h : surjective f) : has_right_inverse f :=
begin
  unfold has_right_inverse,              -- These four lines aren't neeeded for
  unfold function.right_inverse,         -- Lean, but help the human mathematician to 
  unfold function.left_inverse,          -- understand the proof by unfolding
  unfold function.surjective at h,       -- the defintions.
  exact axiom_of_choice h,
end



/-
The situation for left inverse is more complicated. In fact, it isn't even true in general that
an injective function has a left inverse. It's true precisely when the domain of the function is
inhabited (this is roughly the same as saying that the domain is non-empty, when viewed as a set).

In the proof below, we include the hypothesis `d : α`. This asserts that `d` is a term of type `α`.
Knowing this is equivalent to knowing that `α` is inhabited.



Here's a proof sketch:

Suppose `f : α → β`, `h : injective f`, and `d : α`. We want to construct `g : β → α` with the
property that `g (f a) = a`, for every `a : α`.

To begin, take `b : β`. There are two cases.

1. `∃ x : α, f x = b`
2. `¬(∃ x : α, f x = b)`

In the first case, we'll define `g b = x` (we need something like the axiom of choice for this).
In the second case, we'll define `g b = d`, where `d` is the 'default' term in `α` mentioned before.

It remains to show `g` is a left inverse of `f`.

Let `a : α`. We must show `g (f a) = a`. Write `b` for `f a`, so `f a = b`. We must show `g b = a`.
Certainly, `∃ x : α, f x = b`, as witnessed by `a : α`. Let `x : α` be the term used in the
construction to define `g b`, so `f x = b`. Then `g b = x`. It remains to show `x = a`.
But `f x = f a`. By injectivity of `f`, the goal follows.
-/

local attribute [instance] prop_decidable

/-
Finally, here's our proof that every injective function on an inhabited type has a left inverse.
-/
theorem has_left_inverse_of_injective {f : α → β} (h : injective f) (d : α) : has_left_inverse f :=
begin
  unfold has_left_inverse, -- These three lines aren't needed by Lean
  unfold left_inverse,     -- but assist the human matheamtician in
  unfold injective at h,   -- understanding the proof.
  -- Below, we produce the hypothesis required in applying the axiom of choice.
  have h₂ : ∀ b : β, ∃ a : α, (f a = b) ∨ ¬(∃ x : α, f x = b),
  { intro b,
    by_cases k : (∃ x : α, f x = b),
    { cases k with a k₂, -- This is the case where there is some `x` for which `f x = b`.
      use a,
      left,
      exact k₂, },
    { use d,             -- This is the case where there is no such `x`.
      right,
      exact k, }, },
  have h₃ : ∃ g : β → α, ∀ b : β, f (g b) = b ∨ ¬(∃ x : α, f x = b) := axiom_of_choice h₂,
  cases h₃ with g h₄,
  use g,
  intro a,
  let b := f a,
  specialize h₄ b,
  cases h₄ with h₅ h₆,
  { have k₂ : g b = a, from h h₅,
    show g (f a) = a, from k₂, },
  { exfalso,
    apply h₆,
    use a, },
end

/-
Finally, we have a partial converse to the result at the end of the previous file. Namely, we prove
that if `f : α → β` is bijective *and* if `α` is inhabited, then `f` is invertible.
-/
theorem invertible_of_bijective (f : α → β) (d : α) (k : bijective f) : invertible f :=
begin
  cases k with fi fs, -- We have `fi : injective f` and `fs : surjective f`.
  split, -- It suffices to prove `has_left_inverse f` and `has_right_inverse f`.
  { exact has_left_inverse_of_injective fi d, },
  { exact has_right_inverse_of_surjective fs, },
end 

end constructing_inverses

end mth1001
