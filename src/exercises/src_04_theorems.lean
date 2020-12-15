variables p q r : Prop 

namespace mth1001

section theorems

-- Exercise 028:
/-
A theorem is a mechanism for naming a result. By _applying_ a theorem, we can produce new results.
Here is a theorem with its proof left as an exercise.
-/
theorem and_of_and : p ∧ q → q ∧ p :=
begin
  sorry  
end

/-
The _type_ of any expression can be printed to the Infoview using `#check`.
The type of `and_of_and` is
  `∀ (p q : Prop), p ∧ q → q ∧ p`
This means that the theorem takes `p` and `q` propositions (i.e. terms of
type `Prop`) and returns a proof of `p ∧ q → q ∧ p`.

The symbol `∀` is read as 'for all' or 'for every' and is called the
universal quantifier. We'll return to a full explanation of `∀` later.
-/
#check and_of_and

/-
We apply this theorem by subsituting other quantities for `p` and `q`.]
Below, we take `q → r` for `p` and `q ∧ p` for `q` in `and_of_and`.
-/
example : (q → r) ∧ (q ∧ p) → (q ∧ p) ∧ (q → r) :=
and_of_and (q → r) (q ∧ p)

-- Even better, Lean can often infer the arguments to theorems if they
-- are replaced with the `_` placeholder:
example : (q → r) ∧ (q ∧ p) → (q ∧ p) ∧ (q → r) :=
and_of_and _ _

-- We can apply theorems in tactic mode. Using `exact` mimics the term-style proof.
example : (q → r) ∧ (q ∧ p) → (q ∧ p) ∧ (q → r) :=
begin 
  exact and_of_and _ _,
end

/-
We don't need to use `_` here to explicitly request argument inference; the `apply` tactic
does this automatically.
-/
example : (q → r) ∧ (q ∧ p) → (q ∧ p) ∧ (q → r) :=
begin 
  apply and_of_and,
end


-- Exercise 029:
-- Give either a tactic-style or term-style proof of the following.
theorem and_assoc1 : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
sorry 

-- Exercise 030:
-- Using the previous theorem, give a one-line proof of the following.
example (a b : Prop) : ((a → b) ∧ b) ∧ (b → a) → (a → b) ∧ (b ∧ (b → a)) :=
sorry 

-- Exercise 031:
/-
The next example is more challenging. Use `intro`, `apply`, `exact`,
and the previous two theorems.
-/
example (a b : Prop) : ((a → b) ∧ b) ∧ (b → a) → (b ∧ (b → a)) ∧ (a → b) :=
begin
  sorry  end

variables s t u : Prop

-- Exercise 032:
/-
Complete the following proof. The only tactics you are permitted to use are `apply` and `exact`
(each as many times as you like). You can only use these tactics with `and_of_and`,
`and_assoc`, or `h`.
-/
theorem and_assoc2 : s ∧ (t ∧ u) → (s ∧ t) ∧ u :=
begin
  intro h,
  sorry  
end 

end theorems

/-
SUMMARY:

* Theorems in Lean.
* `#check` to find the type of a theorem.
* Using theorems.
-/

end mth1001
