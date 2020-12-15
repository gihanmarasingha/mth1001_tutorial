import tactic.linarith

namespace mth1001

section mixing_quantifiers
/-
Many mathematical results mix quantifiers. The results below states that for every integer
`x`, there exists an integer `y` such that `x + y = 0`.

Here the scope of the universal quantifier is the expression `∃ y : ℤ, x + y = 0`,
whereas the scope of the existential quantifier is the expression `x + y = 0`.

The proof follows the form of the statement. We start by introducing the universal 
quantifier with `intro x`, then introduce the existential quantifier with `use (-x)`.

Note: after issuing `intro x`, the goal is simplified to `∃ y : ℤ, x + y = 0`. The
quantity `x` is fixed and our task is to find `y` for which `x + y = 0`. Clearly, `-x` is
such a value for `y`.
-/
example : ∀ x : ℤ, ∃ y : ℤ, x + y = 0 :=
begin 
  intro x,  -- We let `x` be an arbitrary integer.
  use (-x), -- Take `y` to be `-x`.
  linarith,     -- This closes the goal `x + (-x) = 0`.
end

/-
Changing the order of quantifiers (usually) changes the meaning of a statement. 

Understanding this is very important, so I'll repeat it. 

Changing the order of quantifiers (usually) changes the meaning of a statement.

The statement `∃ y : ℤ, ∀ x : ℤ, x + y = 0`, in which I've merely swapped the order
of quantification in the above result, is false.

To prove this statement would be to find an integer `y` such that for every integer
`x`, `x + y = 0`. 

In greater detail, the scope of the existential quantifier is the expression
`∀ x : ℤ, x + y = 0`. The quantity `y` in this statement is *fixed*. To prove this
statement is to show *for every `x`* that `x + y = 0`.

In particular, taking `x` to be `0`, we must have `0 + y = 0`. But taking `x` to be `1`, we
must have `1 + y = 0`. So `y = 0` *and* `y = -1`. This is a contradiction.
-/

-- Below is a Lean version of the argument above.
example : ¬(∃ y : ℤ, ∀ x : ℤ, x + y = 0) :=
begin
  intro h,
  cases h with y hy,
  have h₁ : y = 0,
  { specialize hy 0,
    linarith, },
  have h₂ : y = -1,
  { specialize hy 1,
    linarith, },
  linarith,
end

-- Exercise 086:
/- Alternatively, we can use `push_neg` to transform the initial goal into
`∀ y : ℤ, ∃ x : ℤ, x + y ≠ 0`. Having done this, we would let `y` be an aribtrary integer and
then choose `x` (which may depend on `y`) so that `x + y ≠ 0`. Can you think of an `x`, depending
on `y`, for which `x + y ≠ 0`? 
-/
example : ¬(∃ y : ℤ, ∀ x : ℤ, x + y = 0) :=
begin
  push_neg,
  sorry  
end


-- Exercise 087:
example : ∃ x : ℤ, ∀ y : ℤ, x + y = y :=
begin
  sorry  
end 


-- Here, `∃ x y : ℤ` is an abbreviation of `∃ x : ℤ, ∃ y : ℤ`.
example : ∃ x y : ℤ, x + y = y + 1 :=
begin 
  use [1, 0], -- This is equivalent to `use 1, use 0`.
  linarith,
end 

-- Exercise 088:
example : ∃ a : ℤ, ∀ b : ℤ, a + b = b :=
begin
  sorry  
end 

-- Exercise 089:
-- Note `∀ x y : ℤ` is an abbreviation of `∀ x : ℤ, ∀ y : ℤ`.
example : ∀ x y : ℤ, x + y = y + x :=
begin
  sorry  
end

/-
Use `push_neg` in proving the next three results.
-/

-- Exercise 090:
example : ¬(∀ x y : ℤ, x + y = x) := 
begin
  sorry    
end

-- Exercise 091:
example : ¬(∀ x : ℤ, ∃ y, x + y = y) := 
begin 
  sorry  
end 

-- The next exercise is quite challenging.
-- Exercise 092:
example : ¬(∃ x y : ℤ, (x + y = 0) ∧ (x * x - y * y = 1)) :=
begin
  sorry    
end  

end mixing_quantifiers

end mth1001
