import tactic.linarith
import .src_05_if_and_only_if

variables p q r : Prop 

namespace mth1001

section rewriting 
/-
Statements of the form `p ↔ q` play a cruicial role in logic. Given `h : p ↔ q`, we can
replace `p`, wherever it appears, with `q`. This is called rewriting.
-/


/-
Here, the `rewrite` tactic (abbreviated to `rw`) is invoked with `h : (p ∧ q) ↔ r`. This
cases Lean to replace `p ∧ q`, wherever it appears in the goal, with `r`.

The goal is reduced to `r ∧ q ∧ r ↔ r ∧ q ∧ r`, which Lean immediately closes.

Note that a one-line tactic proof can be written using `by` rather than enclosing the proof in
a `begin` … `end` block.
-/
example (h : (p ∧ q) ↔ r) : (p ∧ q) ∧ (q ∧ (p ∧ q)) ↔ r ∧ (q ∧ r) :=
by rw h

/-
Below, we use `and_iff_and` (the commutativity of `∧`) together with `and_assoc`
(the associativity of `∧`). Note that `and_iff_and r (q ∧ r)` is the result
`r ∧ (q ∧ r) ↔ (q ∧ r) ∧ r`. 
-/
example (h : (p ∧ q) ↔ r) : (p ∧ q) ∧ (q ∧ (p ∧ q)) ↔ q ∧ (r ∧ r) :=
begin 
  rw h,
  rw and_iff_and r (q ∧ r),
  rw and_assoc q r r,
end

/-
The `rw` tactic can often infer arguments to theorems. In the example above, we can omit
the arguments, leading to the simplified proof below.
-/
example (h : (p ∧ q) ↔ r) : (p ∧ q) ∧ (q ∧ (p ∧ q)) ↔ q ∧ (r ∧ r) :=
begin 
  rw h,
  rw and_iff_and,
  rw and_assoc,
end

-- Several applications of `rw` can be written on one line.
example (h : (p ∧ q) ↔ r) : (p ∧ q) ∧ (q ∧ (p ∧ q)) ↔ q ∧ (r ∧ r) :=
begin 
  rw [h, and_iff_and, and_assoc],
end

#check and_assoc 

/-
We've seen how `rw` can rewrite a goal given a double implication. It can also rewrite a goal
given an equation.

Here, `ℤ` represents the type of integers and is written `\Z`.
-/
example (a b : ℤ) (h : a = b) : a + 2 = b + 2 :=
begin 
  rw h,
end 

/-
Given `h : a = b` or `h : a ↔ b`, we've seen that `rw h` replaces every occurrence of `a` in the
goal with `b`. We can ask for rewriting in the other direction by issuing `rw ←h`, where `←` is
written `\l`. This replaces every occurrence of `b` in the goal with `a`.
-/

/-
Here, we use `rw` with `←`. The `linarith` tactic can solve linear equations and inequalities.

In fact, `linarith` is clever enough to perform the rewriting *without* needing you to specify
it explicitly, so we could omit the line `rw ←h` below.
-/
example (a b : ℤ) (h : 3 + a = b) : b + 3 = a + 6 :=
begin 
  rw ←h,
  linarith,
end


-- Exercise 036:
-- Use `rw` with `←` and the theorems we've proved to solve the following.
example : r ∧ (p ∧ q) ↔ (p ∧ r) ∧ q :=
begin
  sorry  
end 

end rewriting


section implicit_arguments

-- Exercise 037:
/-
Often, it's easier to write a theorem in a form that doesn't require arguments to be specified when
the theorem is applied. We do this by enclosing implicit arguments in braces `{` and `}`.
-/
theorem imp_trans {a b c : Prop} : (a → b) → (b → c) → (a → c) :=
begin 
  sorry  
end

-- Note how the proof of the following complicated result is simply `imp_trans`.
example : (p ∧ q → r) → (r → r ∧ q) → (p ∧ q → r ∧ q) :=
imp_trans 

-- In tactic-form, the proof is `exact imp_trans`.
example : (p ∧ q → r) → (r → r ∧ q) → (p ∧ q → r ∧ q) :=
begin 
  exact imp_trans 
end

/-
As a practical example, we'll use the following result, `add_left_cancel`, which has type
  `∀ {a b c : ℤ}, a + b = a + c → b = c`.
-/
lemma add_left_cancel : ∀ {a b c : ℤ}, a + b = a + c → b = c :=
begin
  intros a b c,
  exact (add_right_inj a).mp
end

/-
We use this result below.
-/
example (x y : ℤ) (h : 2 + x = 2 + y) : x = y :=
add_left_cancel h

-- Exercise 038:
-- Check what the theorem `int.add_comm` asserts. You can prove the following use only this,
-- `int.add_left_cancel`, `have`, `exact`, `rw`, and `apply`.
example (s t u a b : ℤ) (h₁ : s + u = t + u) (h₂ : s + a = t + b) : a = b :=
begin
  have h₃ : u + s =  u + t,
  { sorry, }, 
  sorry    
end 

end implicit_arguments

/-
SUMMARY:

* Using the `rw` tactic to rewrite a goal using an equation or iff.
* Using `←` to use an equation or iff in the opposite direction.

* Implicit arguments to theorems using `{ … }`
-/

end mth1001
