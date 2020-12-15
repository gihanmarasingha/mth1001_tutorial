variables p q r : Prop 

namespace mth1001

section false_and_negation 

/-
`false` is the name of a special proposition from which we can derive anything.
In ordinary mathematics, `false` is written `⊥` and is referred to as an
'arbitrary contradiction' or sometimes just 'contradiction'.

The tactic `exfalso` is used to turn any goal into a proof of `false`.

Side note: `exfalso` is short for the Latin 'ex falso sequitur quodlibet', 
which translates to, 'from a contradiction, whatever you please follows'.
-/

example : false → p :=
begin
  assume h : false, -- I could equally have written `intro h`.
  exfalso, 
  exact h,
end

/-
In term style, `false.elim h` provides a proof of anything, given that `h` is
a proof of `false`.`
-/
example : false → p :=
assume h, false.elim h

/-
An more powerful tactic is `contradiction`. This tactic looks in the context and goal for a
contradition and closes the goal if it finds one.
-/
example : false → p :=
begin 
  contradiction,
end

-- Exercise 057:
-- Use `exfalso` in proving the following result. Try another proof using `contradiction`.
example : (¬p ∨ q) → (p → q) :=
begin
  intros h hp,  /- `intros h hp` is equivalent to `intro h, intro hp`. -/

  sorry  
end


/-
`false` may seem bizzare, but it's just what we need for formalising the notion
of 'not'. The notation `¬p` is an abbreviation for `p → false`. The symbol
`¬` is written `\n`. We read `¬p` as 'not p'. 

In general, to prove `a → b` is to assume `a` and deduce `b`. Thus, to prove
`¬p` is to assume `p` and deduce `false`.
-/

/-
The first thing to observe is that we may derive `false` from `¬p` and `p` by
implication elimination, as `¬p` means `p → false`.
-/
example (h₁ : ¬p) (h₂ : p) : false :=
h₁ h₂

/-
Given it's not the case that you like tea or coffe, one can deduce it's not
the case that you like tea.
-/
example (h : ¬(p ∨ q)) : ¬p :=
begin 
  intro hp, -- Assume hp : p. It remains to prove `false`.
  have hpq : p ∨ q, from or.inl hp,
  show false, from h hpq, -- Or just `h hpq` or `contradiction`.
end

-- Exercise 058:
-- Given `p`, we can derive `¬¬p`. This is part of the law of double negation.
theorem not_not_of_self : p → ¬¬p :=
begin
  intros hp hnp,
  sorry  
end

/-
British mathematician Augustus De Morgan is famous in part for several laws of
logic. We'll build them up from scratch.
-/

-- Exercise 059:
theorem not_or_of_not_and_not : ¬p ∧ ¬q →  ¬(p ∨ q) :=
begin
  intros h hpq, 
  cases hpq with hp hq,
  { sorry, }, 
  { sorry, }, 
end 

-- Exercise 060:
theorem not_and_of_not_or_not : ¬p ∨ ¬q → ¬(p ∧ q) :=
begin
  sorry  
end 

-- Exercise 061:
theorem not_and_not_of_not_or : ¬(p ∨ q) → ¬p ∧ ¬q :=
begin 
  sorry  
end

/-
We'll later see that `p → q` is equivalent to `¬q → ¬p`, the so-called 'contrapositive' of
`p → q`. We prove one direction of this equivalence below.
-/

-- Exercise 062:
example : (p → q) → (¬q → ¬p) :=
begin 
  intros hpq hnq hp,
  sorry  
end 

end false_and_negation 

/-
SUMMARY:

* `false`, the name for an arbitrary contradiction.
* Anything can be proved from false, using `exfalso` (tactic-style) or `false.elim` (term-style).
* The `contradiction` tactic to automate contradiction finding.
* Introducing multiple assumptions with `intros`.
* `¬p` as a shortcut for `p → false`.
* The law of double negation.
-/

end mth1001
