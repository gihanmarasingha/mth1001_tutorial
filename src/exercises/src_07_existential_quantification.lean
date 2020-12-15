import tactic.linarith

namespace mth1001

section existential_quantification

/-
An integer `n` is `even` if there is some integer `m` such that `n = 2*m`. This condition is 
expressed as
  `∃ m, n = 2 * m`,
where the symbol `∃` is called 'the universal quantifier', read as 'there exists' or 'there is',
and typed as `\ex`.
-/

/-
The following is a Lean representation of the above definition.
-/
def even (n : ℤ) := ∃ m, n = 2*m 

/-
To *prove* a particular number `n` is even, it suffices to provide an intger `m` and then
show that `n = 2 *m ` holds.
-/

/-
Below, the goal is initially to show `∃ m, 10 = 2 *m`. The tactic `use 5` removes the
universal quantifier and replaces `m` with `5`, leaving the goal `10 = 2 * 5`.

The tactic `norm_num` closes goals that involve simple arithmetic on numerical expressions.
-/
example : even 10 :=
begin 
  use 5,
  norm_num,
end

-- Exercise 039:
example : even 18 :=
begin
  sorry  
end

/-
We aren't restricted to using numerical expressions. As seen in a previous section, the
`linarith` tactic solves linear equations and inequalities.
-/
variables a b c d : ℤ

example (h : b = 6 * a) : even b :=
begin 
  use (3*a), -- After this tactic, the goal is to prove `b = 2 * (3 * a)`.
  linarith, -- This tactic closes the goal.
end

-- Exercise 040:
example (h₁ : c = 2 * a + 1) (h₂ : d = 2 * b + 1) : even (c + d) :=
begin 
  sorry  
end 

/-
An integer `n` is `odd` if `∃ m, n = 2 * m + 1`.
-/

def odd (n : ℤ) := ∃ m, n = 2 * m + 1 

-- Exercise 041:
example : odd 7 :=
begin
  sorry  
end 

-- Exercise 042:
example (h₁ : c = 2 * a) (h₂ : d = 2 * b + 1) : odd (c + d) :=
begin 
  sorry  
end 

/-
We've seen how to *prove* a number is even or even. Now we'll see how to *apply* the fact that 
a number is even or even.

Given a premise `h : even a`, the tactic `cases h with k hk` removes `h` and introduces into the
context a new variable `k` and the premise `hk : a = 2 * k`. As usual, there is nothing special
about the names `k` or `hk`.
-/

example (h : even a) : even (5*a) :=
begin 
  cases h with k hk,
  use (5*k),
  linarith,
end

-- Exercise 043:
-- Prove that the square of an even number is even.
example (h : even a) : even (a*a) :=
begin 
  sorry  
end

-- Exercise 044:
-- Prove that the sum of two odd numbers is even.
example (h₁ : odd a) (h₂ : odd b) : even (a + b) :=
begin 
  sorry  
end 

-- Exercise 045:
/-
The results of this section can be rewritten to remove any premises, producing statements
that involve implication.

For example, you should only need to add one line to the beginning of a previous proof to
conclude the following.
-/
example : even a → even (a*a) :=
begin
  sorry  
end

end existential_quantification

/-
SUMMARY:

* Definitions in Lean.
* Recap of the `norm_num` and `linarith` tactics.

* Introduction of `∃` via `use`.
* Elimination of `∃` via `cases`.
-/

end mth1001
