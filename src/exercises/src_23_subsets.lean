import data.set
import .src_13_applications_to_even_and_odd
import .src_22_set_equality

open set

namespace mth1001

section subsets

/-
Type `⊆` as `\sub`
-/

/-
Working with particular finite sets, Lean can prove results using `dec_trivial`.
-/
example : ({4, 6, 8} : finset ℤ) ⊆ ({8, 4, 8, 10, 6} : finset ℤ) := dec_trivial

/-
Recall our theorem that for every `a : ℤ`, if `a` is even, then `a * a` is even.
-/
theorem even_square_of_even : ∀ a : ℤ , even a → even (a*a) :=
begin
  intros a h,
  cases h with k hk,
  use (2*k*k),
  rw hk,
  ring, 
end

/-
We'll show that the set of even numbers is a subset of the set of numbers whose square is even.
Lean automatically uses the definition of subset to turn the goal into one of proving
a univerally quantified statement.
-/
example : {x : ℤ | even x} ⊆ {x : ℤ | even (x*x)} := by apply even_square_of_even

-- Here's a proof of the same result that doesn't use `even_square_of_even`.

example : {x : ℤ | even x} ⊆ {x : ℤ | even (x*x)} :=
begin
  intros a h, -- Assume `a : ℤ`, assume `h : a ∈ {x : ℤ | even x}`. 
  rw mem_set_of_eq at *, -- By def. of set membership, `h : even a`. Goal `⊢ even (a*a)`.
  unfold even at h, -- By definition of even, `h : ∃ (m : ℤ), a = 2 * m`.
  cases h with b hb, -- Assume `b : ℤ`, assume `hb : a = 2*b` (exists elim. on `h`)
  -- It suffices to prove `even (a*a)`, i.e. `∃ (m : ℤ), (a*a) = 2*m`
  use (2*b*b), -- By exists introduction on `2*b*b`, it suffices to prove `(a*a)=2*(2*b*b)`.
  rw hb, -- Rewriting with `hb`, the goal is to prove `(2*b)*(2*b)=2*(2*b*b)`.
  ring,  -- This follows by basic arithmetic.
end

open_locale classical

-- Exercise 128:
-- In the following example, we show the converse of the above result. You may wish to refer to
-- the file `src_13_applications_to_even_and_odd.lean` for inspiration.
-- Helpful results and tactics: `even_iff_not_odd`, `not_not`, `contrapose`. 
example : {x : ℤ | even (x*x)} ⊆ {x : ℤ | even x} :=
begin
  rw subset_def, -- We must show `∀ (x : ℤ), x ∈ {x : ℤ | even (x*x)} → {x : ℤ | even x}`
  intro x, -- Assume `x : ℤ`. We must show `x ∈ {x : ℤ | even (x*x)} → {x : ℤ | even x}`
  sorry  
end

-- Exercise 129:
/-
We'll show 'anti-symmetry' of the subset relation. That is, for sets `S` and `T`, we show
`S = T ↔ (S ⊆ T) ∧ (T ⊆ S)`.
-/
theorem subset_antisymm (A : Type*) (S T : set A) : S = T ↔ (S ⊆ T) ∧ (T ⊆ S) :=
begin
  rw ext_iff, -- Rewrite using the definition of set.
  repeat { rw subset_def, }, -- Rewrite (repeatedly) using the definition of subset.
  split,
  { intro h ,
    sorry, }, 
  { intros h x,
    sorry, }, 
end

-- Exercise 130:
-- Transitivity of the subset relation. We prove this from the definition.
theorem subset_trans (A : Type*) (S T U : set A) : (S ⊆ T) ∧ (T ⊆ U) → (S ⊆ U) :=
begin
  repeat { rw subset_def, }, -- Rewrite (repeatedly) using the definition of subset.
  intros h x h₂, -- Assume `h : (S ⊆ T) ∧ (T ⊆ U)`, `x : A`, and `h₂ : x ∈ S`.
  cases h with h₃ h₄, -- Left & right ∧ elim. `h₃ : ∀ x, x ∈ S → x ∈ T`, `h₄ : ∀ x, x ∈ T → x ∈ U`.
  sorry  
end


/-
We'll prove that for all sets `S` and `T` on a type `A`, `¬(S ⊆ T) ↔ ∃ x, x ∈ S ∧ x ∉ T`.
-/
theorem not_subset {A : Type*} (S T : set A): ¬(S ⊆ T) ↔ ∃ x, x ∈ S ∧ x ∉ T :=
begin
  rw subset_def, -- Rewrite using the definition of subset.
  push_neg, -- Negate the universal quantifier and the implication,
  refl, -- The result follows by reflexivity.
end


/-
In the following, we show `{4, 2, 6}` is a subset of the set of even integers.
In Lean, we write the above set as `({4, 2, 6} : set ℤ)`.
Note that the `rcases` tactic decomposes set membership recursively.
-/
example : ({4, 2, -6} : set ℤ) ⊆ {x : ℤ | even x} :=
begin
  intros x h, -- Assume `x : ℤ` and `h : x ∈ {4, 2, 6}`.
  rcases h with hm₆ | h₂ | h₄ | k,
  { use (-3), rw hm₆, norm_num, }, -- The case `x = -6`.
  { use 1, rw h₂, norm_num, }, -- The case `x = 2`.
  { use 2, rw h₄, norm_num, }, -- The case `x = 4`.
  { exfalso, apply k }, -- The case `x ∈ ∅`.
end 

open classical
local attribute [instance] prop_decidable

/-
Let `U = {x : ℤ | x ≤ 8 ∧ x > 4}` and let `S` be the set of even integers. We'll show `¬(U ⊆ S)`.

-/
example : ¬( {x : ℤ | x ≤ 8 ∧ x > 4} ⊆ {x : ℤ | even x} ) :=
begin
  rw not_subset, -- By the `not_subset` result, it suffices to show
  -- `∃ x : ℤ, x ∈ U ∧ x ∉ S`.
  use 5, -- By `∃` intro on `5 : ℤ`, it suffices to prove `5 ∈ U ∧ 5 ∉ S`.
  split, -- By and introduction, it suffices to prove 1. `5 ∈ U` and 2. `5 ∉ S`.
  { split; -- By and introduction, it suffices to prove `5 ≤ 8` and `5 > 4` }
    -- The semi-colon (rather than comma) here means, 'apply the following tactic to *both* goals'.
      norm_num, -- We close both goals `5 ≤ 8` and `5 > 4` with norm_num.
  },
  { rw nmem_set_of_eq, -- Rewriting by definition of `∉`, the goal is to show `¬even 5`.
    rw even_iff_not_odd, -- Equally, to show `¬¬odd 5`.
    rw not_not, -- By double negation, we must show `odd 5`, i.e. `∃ m : Z, 5 = 2 * m + 1`.
    use 2, -- By `∃` intro with `2`, it suffices to show `5 = 2 * 2 + 1`.
    norm_num, -- We close the goal with `norm_num`.     
  }
end

/-
We show the subset relation is not symmetric via a counterexample.
We aim to show `¬ (∀ S T, S ⊆ T → T ⊆ S)`.
-/
example : ¬(∀ A : Type*, ∀ S T : set A, S ⊆ T → T ⊆ S) :=
begin
  push_neg, -- Push the negation inside the goal to tranform it to
  -- `∃ (A : Type*), ∃ S T : set A, S ⊆ T ∧ ¬(T ⊆ S)`.
  use [ℤ, {1, 2}, {1, 2, 3}], -- Take `A = ℤ`, `S = {1, 2}`, and `T = {1, 2, 3}`.
  split,
  { exact subset_insert 3 {1, 2} }, -- `{1, 2, 3}` is the set construct by inserting `3`
  -- into the set `{1, 2}`, so `{1, 2}` is a subset of `{1, 2, 3}`.
  { rw subset_def, -- Rewrite the goal using the definition of subset.
    intro h, -- Assume `h : ∀ x, x ∈ {1, 2, 3} → x ∈ {1, 2}`.
    specialize h 3, -- By `∀` elim. on `h` with `3`, we have `h : 3 ∈ {1, 2, 3} → 3 ∈ {1, 2}`.
    contrapose! h, -- Negating, the goal is equivalent to `3 ∈ {1, 2, 3} ∧ 3 ∉ {1, 2}`.
    split; -- By and introduction, it suffices to prove 1. `3 ∈ {1, 2, 3}` and 2. `3 ∉ {1, 2}`.
      norm_num, }, -- Close both goals by `norm_num`.
end

end subsets

end mth1001
