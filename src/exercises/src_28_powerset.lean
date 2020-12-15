import data.set

open set

namespace mth1001

variable A : Type*
variables (S T : set A)

#check powerset
#check mem_set_of_eq
#check mem_union_eq
#check subset_def
#check subset_union_left

/-
Type `𝒫` as `\power`
-/

example : (𝒫 S) ∪ (𝒫 T) ⊆ 𝒫 (S ∪ T) :=
begin
  -- Using the definition of subset, we must show, `∀ x, x ∈ 𝒫 S ∪ 𝒫 T → x ∈ 𝒫 (S ∪ T)`.
--  rw subset_def, 
  intro x, -- Assume `x : U`.
  intro h, -- Assume `h : x ∈ 𝒫 S ∪ 𝒫 T`.
  rw mem_union_eq at h, -- By definition, `h : x ∈ 𝒫 S ∨ 𝒫 T`.
  /-
  By or elim., it suffices to prove the goal under the assumptions
  1. `h₂ : x ∈ 𝒫 S`,
  2. `h₃ : x ∈ 𝒫 T`.
  -/
  -- By repeated definion of 𝒫 and ∈, `h : x ⊆ S ∨ x ⊆ T`. The goal is `x ⊆ S ∪ T`.
  repeat { rw [powerset, mem_set_of_eq] at *, }, 
  cases h with h₂ h₃,
  { have h₄ : S ⊆ S ∪ T, from set.subset_union_left S T,
    transitivity,
    { exact h₂,}, 
    { exact h₄, }, },
  { transitivity,
    { exact h₃, },
    { exact set.subset_union_right S T, }, },
end

/-
The converse of the above result is *not* true. Here's a proof by counterexample.
-/
example : ¬(∀ A : Type*, ∀ S T : set A, 𝒫 (S ∪ T) ⊆  (𝒫 S) ∪ (𝒫 T)) :=
begin
  push_neg, -- Negating, the goal is `∃ A, ∃ S T : set A, ¬(𝒫 (S ∪ T) ⊆ 𝒫 S ∪ 𝒫 T)`.
  use [ℤ, {1}, {2}], -- We'll take `A` as `ℤ`, `S` as `{1}` and `T` as `{2}`.
  repeat { rw powerset },    -- Apply repeatedly the definitions of powerset
  repeat { rw subset_def },  -- and subset,
  norm_num, -- negating and noting `{1} ∪ {2} = {2, 1}`, the goal is to prove
  -- `∃ (x : set ℤ), x ⊆ {2, 1} ∧ ¬(x ⊆ {1} ∨ x ⊆ {2})`
  use {1, 2}, -- We take `{1, 2}` for `x`.
  split, /- It suffices to prove the two goals:
  1. `{1, 2} ⊆ {2, 1}` and
  2. `({1, 2} ⊆ {1} ∨ {1, 2} ⊆ {2})`
  -/
  { rw subset_def, -- We solve the first subgoal by definition of subset
    finish, },     -- and rules of logic.
  { repeat { rw subset_def }, -- By repeated application of the definition of subset
    push_neg, -- and negating, we must show
    -- `(∃ (x : ℤ), x ∈ {1, 2} ∧ x ∉ {1}) ∧ ∃ (x : ℤ), x ∈ {1, 2} ∧ x ∉ {2}`.    
    split, /- By and introduction, this splits into two subgoals:
    2.1. `∃ (x : ℤ), x ∈ {1, 2} ∧ x ∉ {1}`.
    2.2. `∃ (x : ℤ), x ∈ {1, 2} ∧ x ∉ {2}`.
    -/
    { use 2, finish, }, -- We close the goal by showing `2 ∈ {1, 2} ∧ 2 ∉ {1}`.
    { use 1, finish, }, }, -- We close the goal by showing `1 ∈ {1, 2} ∧ 1 ∉ {2}`.
end

-- Exercise 141:
example : (𝒫 S) ∩ (𝒫 T) ⊆ 𝒫 (S ∩ T) :=
begin
  sorry  
end

-- Exercise 142:
example : 𝒫 (S ∩ T) ⊆ (𝒫 S) ∩ (𝒫 T) :=
begin
  sorry  
end


end mth1001
