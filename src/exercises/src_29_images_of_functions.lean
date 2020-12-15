import data.set
import .src_17_even_odd_further

open set function

namespace mth1001

section images_of_functions

/-
Suppose `U` and `V` are types, that `f : U → V` is a function with domain `U` and codomain `V`.

Given a set `A : set U`, the *image* of `A` under `f` is the set
`{v : V | ∃ u : U, u ∈ A ∧ f u = v}`.

In less formal language, we write this as `{f u | u ∈ A}`.

Lean denotes this image as `image f A` or `f '' A`. Mathematicians typically write the image of `A`
under `f` as `f (A)`. Note `A` is a set and so is `f (A)`.
-/

section image_example

/-
For example, we'll define a function `f : ℤ → ℤ` by `f n = 2 * n + 6`. We'll take `A` to be the
set of integers and we'll show that `image f A` is the set of even integers.
-/

def f (n : ℤ) : ℤ := 2 * n + 6
def A : set ℤ := {x | true} -- This is the set of all integers

example : f '' A = {y | even y} :=
begin
  ext,  -- Assume `x : ℤ`. It suffices to show `x ∈ f '' A ↔ x ∈ {y : ℤ | even y}`.
  split, -- Decompose the `↔` into two implication proofs.
  { rintro ⟨n, ⟨_, h₂⟩⟩, -- `rintro` is intro followed by recursive application of `cases`.
    -- Used here, we have `h₂ : f n = x` with a goal `x ∈ {y : ℤ | even y}`.
    use (n + 3), -- It suffices to show `x = 2 * (n + 3)`.
    rw ←h₂, -- Equally, to show `f n = 2 * (n + 3)`.
    unfold f, -- In other words, to show `2 * n + 6 = 2 * (n + 3)`.
    linarith, }, -- Which follows by linear arithmetic.
  { rintro ⟨m, h₂⟩, -- Assume `m : ℤ` and `h₂ : x = 2 *m`. It suffices to show `x ∈ f '' A`.
    use (m - 3), -- It suffices to show `m - 3 ∈ A ∧ f (m - 3) = x`.
    split,
    { unfold A, }, -- It's trivially true that `m - 3 ∈ A` as `A` is the set of all integers.
    { unfold f, -- It suffices to show `2 * (m - 3) + 6 = x`.
      rw h₂, -- That is, we must show `2 * (m - 3) + 6 = 2 * m`.
      linarith, }, }, -- Which holds by linear arithmetic.
end

end image_example

section image_theorems

variable {α : Type*}
variable {β : Type*}
variables S T : set α

-- The image of a union of the union of images.
theorem image_union (f : α → β) : f '' (S ∪ T) = f '' S ∪ f '' T :=
begin
  ext,
  split,
  { rintro ⟨a, hs | ht, rfl⟩,
    { rw mem_union_eq,
      left,
      use a,
      cc, },
    { right,
      use a,
      cc, }, },
  { rintro (⟨a, hs, rfl⟩ | ⟨a, ht, rfl⟩),
    { use a,
      split,
      { left, exact hs, },
      { refl, }, },
    { use a,
      split,
      { right, exact ht, },
      { refl, }, }, },
end

-- Exercise 143:
-- The image of an intersection is a subset of the intersection of the images.
theorem image_inter_subset (f : α → β) : f '' (S ∩ T) ⊆ f '' S ∩ f '' T :=
begin
  rw subset_def,
  sorry    
end


/-
The reverse inclusion of the above theorem is false. That is, there exist types `α`, `β`,
there exists a function `f : α → β`, there exist sets `S : set α` and `T : set β` such that
`¬(f '' S ∩ f '' T ⊆ f '' (S ∩ T))`.

Can you find a counterexample?
-/

end image_theorems

end images_of_functions


end mth1001
