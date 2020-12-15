import .src_10_false_and_negation

variables p q r : Prop

namespace mth1001

section lem 

/-
The law of the excluded middle asserts `p ∨ ¬p`, for any proposition `p`. Together with 
or elimination, this leads to a proof method called 'proof by cases' or 'proof by exhaustion'.

Suppose we wish to prove `q`. By the law of the excluded middle, we have `p ∨ ¬p` (for any `p`).
If we can prove both `p → q` and `¬p → q`, then, by or elimination, we have a proof of `q`.

In summary, to prove `q`, it suffices to show both `p → q` and `¬p → q`.
-/

/-
This pattern of reasoning is caputured by the tactic `by_cases`. If `p` is a propostion and if `q`
is the current goal, then `by_cases k : p` replaces the goal `q` with two subgoals, both to solve
`q`, but with `k : p` in the  context of the first subgoal and `k : ¬p` in the context of the
second. There is nothing special here about the names `p`, `q`, or `k`.
-/

/-
To use `by_cases`, we first open the `classical` namespace and then
instruct Lean to treat all propostions as 'decidable'. You don't need to know what this means.
-/
open classical
local attribute [instance] prop_decidable

example (h₁ : p → q) (h₂ : ¬p → q) : q :=
begin 
  by_cases k : p,
  { exact h₁ k, },
  { exact h₂ k, },
end

/-
The following term-style proof explicitly uses or elimnation and the law of the excluded middle. 
Here, `classical.em p` is a proof of `p ∨ ¬p`.
-/
example (h₁ : p → q) (h₂ : ¬p → q) : q :=
or.elim (classical.em p) h₁ h₂ 


-- Exercise 063:
-- Complete the following proof of one direction of one of De Morgan's laws.
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
begin 
  intro h,
  by_cases k : p,
  { right,
    intro hq,
    exact h ⟨k, hq⟩, },
  { sorry, }, 
end 

-- Exercise 064:
-- We'll now show one can deduce `¬p ∨ q` from `p → q`.
example : (p → q) → (¬p ∨ q) :=
begin 
  sorry  
end

end lem 


section reductio 

/-
Proof by contradiction is another method of reasoning closely associated with the
law of the excluded middle. 

If, on the assumption of `¬p`, one can derive `false`, then one has `p`.
-/

open classical
local attribute [instance] prop_decidable

/-
If the current goal is to prove `p`, the `by_contradiction` tactic introduces a new premise
`a : ¬p` into the context and replaces the goal with `false`.

Below, we invoke the tactic as `by_contradiction k`. With this variant, we specify the name
of the new premise to be `k`, thereby introducing `k : ¬p` into the context.
-/
example (h : ¬p → false) : p :=
begin 
  by_contradiction k,
  exact h k,
end 

-- Exercise 065:
-- Using proof by contradiction, we have the remaining part of the law of double negation.
theorem self_of_not_not : ¬¬p → p :=
begin 
  intro hnnp,
  by_contradiction hnp,
  sorry  
end

-- Exercise 066:
-- Combine our two previous results to show `¬¬p ↔ p`.
theorem not_not {p : Prop} : ¬¬p ↔ p :=
begin
  sorry  
end

-- Exercise 067:
-- We show the remaining part of the equivalence of `p → q` with its contrapositive. 
example : (¬q → ¬p) → (p → q) :=
begin 
  sorry  
end

-- Exercise 068:
/- 
We can prove one direction of one of of De Morgan's laws using proof by contradiction.
Complete the following proof using only the `intro`, `by_contradiction`, `apply`, `split`,
`exact`, `left`, and `right` tacitcs. You may need to use `by_contradiction` more than once.
 -/
theorem not_or_not_of_not_and : ¬(p ∧ q) → ¬p ∨ ¬q :=
begin 
  sorry  
end

end reductio

/-
SUMMARY:

* The law of the excluded middle: `p ∨ ¬p` holds for every `p`.
* Proof `by_contradiction`. To prove `p`, we assume `¬p` and derive `false`.
-/

end mth1001
