import .src_09_or_elimination

namespace mth1001

section applications_to_even_and_odd

/-
In this section, we'll show applications of the law of the excluded middle, contradiction, 
and contrapositive.
-/

/-
Here's a very short proof that `0 ≠ 1`, where `≠` is typed as `\ne`. The goal is closed using
the `linarith` tactic, which can solve linear equations and inequalities.

Note the use of `by` instead of the `begin` … `end` block. Also note that we type `(0 : ℤ)`; this
specifies that the theorem refers to the `0` in `ℤ` rather than any other `0`.
-/
theorem zero_ne_one : (0 : ℤ) ≠ 1 := by linarith

/-
We use this to prove that `0` is not odd. Again, you don't need to understand the details
of the proof.
-/
theorem not_odd_zero : ¬(odd (0 : ℤ)) :=
begin 
  rintro ⟨k, hk⟩,
  apply zero_ne_one,
  rw [←(int.zero_mod 2), hk, add_comm, int.add_mul_mod_self_left],
  refl,
end

example : ¬(odd (0 : ℤ)) :=
begin 
  rintro ⟨k, hk⟩,
  apply zero_ne_one,
  rw [←(int.zero_mod 2), hk, add_comm, int.add_mul_mod_self_left],
  refl,
end


-- Exercise 074:
/-
In a previous section, we proved that every integer `n` is even or odd. However, we haven't
yet discounted the possiblity that there is some integer `n` that is *both* even and odd.

Use `linarith` to solve any equations that arise.
-/
theorem not_exists_even_and_odd : ¬ (∃ m, even m ∧ odd m) :=
begin 
  intro h,
  cases h with k hk,
  cases hk with evenk oddk,
  cases evenk with a ha,
  cases oddk with b hb,
  sorry  
end 

/-
For those wishing to spend the least amount of time typing, note that Lean offers tactics
`rcases` and `rintro`. Their use use best illustrated by the following in which I have
replaced the first five lines of the above example with only two.
-/
example : ¬(∃ m, even m ∧ odd m) :=
begin 
  rintro ⟨k, hk⟩,
  rcases hk with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, 
  sorry  
end 

-- Exercise 075:
/-
As a consequence, we'll show an integer is even if and only if it is not odd.
-/
theorem even_iff_not_odd {a : ℤ} : even a ↔ ¬(odd a) :=
begin 
  sorry    
end 

-- Exercise 076:
-- We need an auxiliary result, that the square of an odd number is odd.
theorem odd_square_of_odd {b : ℤ} : odd b → odd (b*b) :=
begin
  sorry  
end

/-
Given a statement `p → q`, its *converse* is the statement `q → p`. Given an integer `a`, we've
proved `even a → even (a*a)`. Our aim is to prove the converse of the statement, namely
`even (a*a) → even a`.
-/

-- Exercise 077:
/-
The following theorem can be proved using only `contrapose`, `contrapose!`, `intro`, `apply`, and
`exact`, together with the results `even_iff_not_odd` and `odd_square_of_odd`.

Recall that if `h : p ↔ q`, then `h.mp : p → q` and `h.mpr : q → p`.
-/
example (b : ℤ) : even (b*b) → even b :=
begin 
  contrapose,
  intro hneven,
  have h₁ : odd (b*b) → ¬(even (b*b)),
  { sorry, }, 
  sorry  
end 

end applications_to_even_and_odd

/-
SUMMARY:

* Applications of previous work.
* Using `rcases` and `rintro` as recursive versions of `cases` and `intro`.
-/

end mth1001
