import .src_07_existential_quantification

variables p q r : Prop 

namespace mth1001

section or_introduction

/-
Given `p`, we know `p ∨ q`. Given `q`, we know `p ∨ q`. This is called or introduction.
The symbol `∨` is written `\or`.
-/

-- Left or introduction
example (h : p) : p ∨ q :=
or.inl h

-- Right or introduction
example (h : q) : p ∨ q :=
or.inr h

-- Tactic style
example (h : p) : p ∨ q :=
begin 
  left,
  exact h,
end

-- Exercise 046:
example (h : q) : p ∨ q :=
begin
  sorry  
end

/-
Recall that any result with premises can be translated into a result without premises via
implication introduction.
-/
example : p → p ∨ q :=
assume h : p,
  or.inl h

-- Exercise 047:
-- Give a tactic-style proof of the above.
example : p → p ∨ q :=
begin
  sorry  
end

-- Exercise 048:
-- The following example is a little more challenging.
example : p ∧ q → p ∨ q :=
begin 
  sorry  
end


-- Exercise 049:
-- We return to looking at odd numbers. Refer back to the section on existential quantification.
example (n : ℤ) : (∃ m, n = 4 *m + 3) → (odd 10) ∨ (odd n) :=
begin 
  sorry  
end

end or_introduction

/-
SUMMARY:

* Or introduction.
* Term-style introduction using `or.inl` or `or.inr`.
* Tactic-style introduction using `left` or `right`.
-/

end mth1001
