import tactic.linarith

namespace mth1001

section negating_quantifiers 

/-
We *can* deal with negated quantified statements using `intro`, as we did before for other
negated statements.
-/

-- Exercise 081:
-- Finish the proof below using `specialize` and `linarith`.
-- *Note*, `linarith` can prove `false` if there is a contradiction amongst the premises.
example : ¬(∀ x : ℤ, 2 * x + 6 = 0) :=
begin 
  intro h,
  sorry  
end

/-
A more natural approach is to recognise that `¬(∀ x, P x)` can always be rewritten as
`∃ x, ¬(P x)`, where `P` is any function (more accurately a *predicate*) depending on `x`.
The Lean tactic `push_neg`, which we've seen before, accomplishes this transformation.
-/

-- Exercise 082:
-- Below, `push_neg` transforms the goal into `∃ x : ℤ, 2 * x + 6 ≠ 0`.
example : ¬(∀ x : ℤ, 2 * x + 6 = 0) :=
begin 
  push_neg,
  sorry  
end

-- Exercise 083:
-- Solve the following using `push_neg`
example : ¬(∀ x : ℤ, x > 5) := 
begin 
  sorry  
end 


/-
Negating existential quantifiers follows a similar principle. We begin by using `intro`.
-/


-- Exercise 084:
-- Use `cases` and `linarith` to prove the following result.
example : ¬(∃ x : ℤ, (x + 2 ≥ 3) ∧ (2 * x + 10 ≤ 8)) :=
begin 
  intro h,
  sorry  
end 

-- Exercise 085:
/-
An alternative approach is to recognise that `¬(∃ x, P x)` is equivalent to `∀ x, ¬(P x)`.

Lean offers this method via `push_neg`. Finish the proof below.
-/
example : ¬(∃ x : ℤ, (x + 2 ≥ 3) ∧ (2 * x + 10 ≤ 8)) :=
begin 
  push_neg,
  intro x,
  by_cases h : x + 2 < 3,
  { sorry, }, 
  { sorry, }, 
end

end negating_quantifiers

end mth1001
