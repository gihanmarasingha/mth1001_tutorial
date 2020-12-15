import tactic.linarith

namespace mth1001

section inequalities_and_upper_bounds

/-
At the start of this module, we looked at simple inequalities. We'll extend our study to
consider bounds and greatest bounds.

These considerations will later form the basis of our study of suprema of sets of real numbers.
-/

-- Given, `x ≤ 2`, we can prove `3 * x + 8 ≥ 5 * x`.
-- Below, `∀ x ≤ 2, 3 * x + 8 ≥ 5 * x` is an abbreviation of `∀ x, x ≤ 2 → 3 * x + 8 ≥ 5 * x`.
example : ∀ x ≤ 2, 3 * x + 8 ≥ 5 * x :=
begin 
  intros x hx,
  linarith,
end 

-- Exercise 100:
example : ∀ x ≤ 0, 3 * x  + 8 ≥ 5 * x :=
begin 
  sorry  
end 


/-
We can generalise the above, writing `x ≤ y` instead of `x ≤ 2` or `x ≤ 0`. However, it simply
isn't true *for every `y`* that if `x ≤ y`, then `3 * x + 8 ≥ 5 * x`. We ask you to prove this
below.
-/

-- Exercise 101:
example : ¬(∀ y, ∀ x, x ≤ y → 3 * x + 8 ≥ 5 * x) :=
begin 
  sorry  
end

/-
However, if we impose constraints on `y`, for instance, given `y ≤ 3`, given `x ≤ y`, you can 
prove `3 * x + 8 ≥ 5 * x`.
-/

-- Exercise 102:
example : ∀ y ≤ 1, ∀ x ≤ y, 3 * x + 8 ≥ 5 * x :=
begin 
  sorry    
end 

/-
Now `1` isn't the only bound for `y`.
-/

-- Exercise 103:
example : ∀ y ≤ 0, ∀ x ≤ y, 3 * x + 8 ≥ 5 * x :=
begin 
  sorry  
end 

-- Exercise 104:
/-
We can generalise further, writing `y ≤ z` instead of `1` or `0` above. Once more, however, it
isn't true that *for every* `z`, given `y ≤ z`, given `x ≤ y`, one has `3 * x + 8 ≥ 5 * x`.
-/
example : ¬(∀ z, ∀ y ≤ z, ∀ x ≤ y, 3 * x + 8 ≥ 5 * x) :=
begin 
  sorry  
end

/-
We'll write a new definition `is_bnd_ineq` so that `is_bnd_ineq z` holds if, given `y ≤ z`,
given `x ≤ y`, one has `3 * x + 8 ≥ 5 * x`.
-/

def is_bnd_ineq (z : ℤ) := ∀ y ≤ z, ∀ x ≤ y, 3 * x + 8 ≥ 5 * x

/-
With this definition, we can rephrase some of the results above. The proofs are no different.
-/

-- Exercise 105:
example : is_bnd_ineq 1 :=
begin
  unfold is_bnd_ineq, -- This line isn't necessary for Lean, but helps the human proof writer!
  sorry  
end

-- Exercise 106:
example : is_bnd_ineq 0 :=
begin
  sorry  
end

/-
We come now to the main definition of this section. What does it mean to be a *greatest* bound?
`z` is a greatest bound if:
* `z` is a bound (i.e. we have `is_bnd_ineq z`) and
* For every `w`, if `w` is a bound, then `w ≤ z`.
-/

def greatest_bnd_ineq (z : ℤ) :=
is_bnd_ineq z ∧ (∀ w, is_bnd_ineq w → w ≤ z)

/-
The main task of this section is to prove `greatest_bnd_ineq 4`, i.e that `4` is a greatest bound.
-/

-- Exercise 107:
example : greatest_bnd_ineq 4 :=
begin 
  sorry  
end

/-
We'd like to conclude that `4` is *the* greatest bound, but we haven't proved that there is only
one greatest bound. This, we proceed to do.
-/

-- Exercise 108:
example (z₁ z₂ : ℤ) : greatest_bnd_ineq z₁ ∧ greatest_bnd_ineq z₂ → z₁ = z₂ :=
begin 
  intro h,
  rcases h with ⟨⟨bnd₁, gt₁⟩, bnd₂, gt₂⟩,
  have : z₁ ≤ z₂,
  { sorry, }, 
  have : z₂ ≤ z₁,
  { sorry, }, 
  linarith,
end 

end inequalities_and_upper_bounds

end mth1001
