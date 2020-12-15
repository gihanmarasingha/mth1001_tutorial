import tactic.push_neg 
import .src_11_lem_reductio

variables p q r : Prop 

namespace mth1001

section contrapositive
/-
Recall that the contrapositive of the statement `p → q` is the statement `¬q → ¬p`.

Lean has a tactic `contrapose` that turns any goal of the form `p → q` into its contrapositive.
-/

example (h : ¬q → ¬p) : p → q :=
begin
  contrapose,
  exact h,
end 

/-
Below, `contrapose` replaces `¬q → ¬p` with its contrapositve, `¬¬p → ¬¬q`. We simplify this
expression using our result `not_not` which asserts `¬¬a ↔ a`, for any proposition `a`.
-/
example (h : p → q) : ¬q → ¬p :=
begin 
  contrapose,
  rw [not_not, not_not],
  exact h,
end 

/-
Instead of `not_not`, we can use the tactic `push_neg`, a big bag of tricks used to push a negation
inside the goal. 
-/
example (h : p → q) : ¬q → ¬p :=
begin 
  contrapose,
  push_neg,
  exact h,
end

-- Exercise 069:
/-
Using only the tactics `push_neg`, `intro`, and `exact`, prove the following,
which we've seen as `not_and_of_not_or_not`.
-/
example : (¬p ∨ ¬ q) → ¬(p ∧ q) :=
begin
  sorry  
end 

-- Exercise 070:
-- We can use `contrapose` to reprove `not_or_not_of_not_and`. Don't use `push_neg` in this example.
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
begin 
  contrapose,
  rw not_not,
  intro h,
  have h₁ : p ↔ ¬¬p, from not_not.symm,
  sorry  
end 

/-
The above result is proved easily using the combination of `contrapose` and `push_neg`. In fact,
this is such a commmon combination that Lean offers it as the single tactic `contrapose!`.
-/

example : (¬q → ¬p) → (p → q) :=
begin 
  intro h,
  contrapose!,
  exact h,
end

-- Exercise 071:
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
begin
  contrapose!,
  sorry  
end

/-
A typical first step in proving a goal `p → q` is implication introduction, applying the tactic
`intro h₁` (say) to introduce the premise `h₁ : p` and changing the goal to `q`.

Sometimes, it's useful to go in the other direction. In the following example, the goal is `q`
while there are premises `h₁ : p` and `h₂ : ¬q → ¬p`.

The `revert` tactic 'puts back' the premise `h₁ : p`, transforming the goal into `p → q` and
removing `h₁`. After reversion, the goal is amenable to the `contrapose` tactic.
-/
example (h₁ : p) (h₂ : ¬q → ¬p) : q :=
begin 
  revert h₁,
  contrapose,
  exact h₂,
end

-- Exercise 072:
-- Prove the following using `revert`, `apply`, and `not_or_not_of_not_and`.
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
begin
  sorry  
end

/-
An alternative to `revert` is to use `contrapose` with the name of a premise. At the point of
application in the proof below, the goal is `q` and `h₁` is the assertion `h₁ : p`. Focussing just
on this premise and the goal, we have to prove `p → q`. The contrapositive is `¬q → ¬p`.
The application `contrapose h₁` replaces the goal with `¬p` and replaces `h₁` with `h₁ : ¬q`.
-/
example (h₁ : p) (h₂ : ¬q → ¬p) : q :=
begin 
  contrapose h₁,
  exact h₂ h₁,
end

-- Exercise 073:
-- Prove the following using the `revert`, `rw`, `apply`, `exact`, `contrapose`, tactics with
-- the results `not_not` and `not_and_not_of_not_or`.
example (h : ¬(p ∧ q) ) : ¬p ∨ ¬q :=
begin 
  have k : ¬(¬¬p ∧ ¬¬q),
  { sorry, }, 
  sorry  
end 

end contrapositive

/-
SUMMARY:

* The contrapositive of `p → q` is `¬q → ¬p`.
* The `contrapose` tactic changes a goal into its contrapositive.
* Given `⊢ q` and `h : p`, `contrapose h` produces `⊢ ¬p` and `h : ¬q`.
* The `push_neg` tactic pushes a negation into a goal or premise.
* `contrapose!` is a combination of `contrapose` and `push_neg`.
* The `revert` tactic puts a premise back into the goal.
-/

end mth1001
