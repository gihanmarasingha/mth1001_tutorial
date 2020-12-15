import .src_05_if_and_only_if
import .src_07_existential_quantification

namespace mth1001

section universal_quantification_introduction

/-
The symbol `∀`, written `\all`, is called the universal quantifier. 
It corresponds roughly to the English phrases 'for all' or 'for every'.#check
-/


/-
Most of our results above implicitly involve the universal quantifier. The command below shows that
`and_iff_and` asserts:
  `∀ (p q : Prop), p ∧ q ↔ q ∧ p`.
This is an abbreviation of the longer
  `∀ (p : Prop), ∀ (q : Prop), p ∧ q ↔ q ∧ p`


In English, this says, 'for every proposition `p`, for every proposition `q`, `p` and `q` if and
only if `q` and `p`.`
-/
#check and_iff_and

/-
We can *explicitly* prove universally quantified statements (i.e. introduce the universal 
quantifier) by using `intro`, much as we do in implication introduction.
-/
theorem even_square_of_even : ∀ m : ℤ, even m → even (m*m) :=
begin 
  intro m, -- In English, we'd write, 'Let `m` be an integer`.
  rintro ⟨k, hk⟩,
  use (2*k*k),
  rw hk,
  ring,
end

-- Exercise 078:
example : ∀ m : ℤ, odd m → odd (m*m) :=
begin 
  sorry  
end 

-- Exercise 079:
/-
Statements involving multiple universal quantifiers can be proved using multiple applications of
`intro`, or by using `intros`.
-/
example : ∀ (a b : Prop), a ∧ b ↔ b ∧ a :=
begin 
  intros a b,
  split,
  { sorry,} , 
  { sorry,} , 
end

end universal_quantification_introduction


section universal_quantification_elimination
/-
Elimination of the universal quantifier has similar syntax to implication elimination. 
-/
example (h : even 10) : even (10*10) :=
(even_square_of_even 10) h

/-
In the above example, `even_square_of_even 10` is the stament that results from eliminating the
universal quantifier to give `even 10 → even (10*10)`. We now use implication elimination,
applying this result to `h : even 10`, to give `even (10*10)`.

When applying statements or functions, Lean treats `f x y` to be the same as `(f x) y`, so the
above proof can be written more simply as folllows.
-/
example (h : even 10) : even (10*10) :=
even_square_of_even 10 h

/-
The tactic approach offers two other ways to eliminate the universal quantifier. We can use `apply`.
-/
example (h : even 10) : even (10*10) :=
begin
  apply even_square_of_even, -- This does both `∀`-elimination and `→`-elimination.
  exact h,
end

/-
If the universallly quantified statement is in the context, we can use `specialize`.
-/
example (h₁ : ∀ m, even m → even (m*m)) (h₂ : even 10): even (10*10) :=
begin 
  specialize h₁ 10,
  exact h₁ h₂,
end

-- Exercise 080:
-- Solve the following using `specialize`, `have`, `linarith`, and `exact`.
example (y z : ℤ) (h₁ : ∀ x : ℤ, x ≥ 0 → x + y ≥ y) (h₂ : z ≥ -2) : (z + 2) + y ≥ y := 
begin 
  sorry  
end 

end universal_quantification_elimination

end mth1001
