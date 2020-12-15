variables p q r : Prop

namespace mth1001

section and_elimination

/-
In the following examples, we have a single premise `h : p ∧ q`.
This can be read as '`h` a proof (or the assumption) of `p ∧ q`'.
From this premise, we deduce `p`.

Note: `∧` can be entered by typing `\and`
-/

/-
The first example presents a 'term-style' proof, as opposed to the 'tactic-style' proofs in
the previous section. In standard maths, this says:

  Given `h : p ∧ q`, `p` follows by left and elimination on `h`.

We can even omit the label of the premise in standard maths and write:

  Given `p ∧ q`, `p` follows by left and elimination.

-/
example (h : p ∧ q) : p :=
h.left

-- The second term-style proof is similar, but with `1` in place of `left`.
example (h : p ∧ q) : p :=
h.1

-- Exercise 007:
-- Replace the `sorry` below with a proof and write out the example in standard maths.
example (h : p ∧ r) : p :=
sorry 
-- Exercise 008:
-- Guess what to write instead of `h.left` in the next example!
example (h : p ∧ q) : q :=
sorry 

-- Exercise 009:
example (k : p ∧ q) : p :=
sorry 

-- Exercise 010:
-- Replace each occurrence of `sorry` below with appropriate text to
-- give a proof of `r` from the premise `k : q ∧ r`.
example (k : q ∧ r) :sorry :=
sorry 

/-
Lean's 'tactic mode' admits a more relaxed proof-writing style. We'll later see that it gives
access to Lean's powerful proof automation features.

As an exercise, list the tactics you've seen so far.
-/

/-
The `exact` tactic is used to close the goal using one of the premises or statements Lean already
knows.
-/

/-
In stanard maths, the following states:

  Given `h₁ : 3 + 3 = 7` and `h₂ : 1 + 1 = 2`, `3 + 3 = 7` follows, by `h₁`.

or

  Given `3 + 3 = 7` and `1 + 1 = 2`, `3 + 3 = 7` follows, by the premise `3 + 3 = 7`.

In Lean, we close the goal using `exact h₁`.
-/
example (h₁ : 3 + 3 = 7) (h₂ : 1 + 1 = 2) : 3 + 3 = 7 :=
by exact h₁

/-
In the example above, we had two premises. The set of premises and other statements proved during
the course of a proof is called the _context_. Usually, as we work our way through a proof, we
add intermediate statements to the context as we prove them.
-/

-- Exercise 011:
-- Complete the Lean proof and translate into standard maths.
example (h₁ : 4 ≤ 0) (h₂ : 7 = 3 + 4) (h₃ : 10 ≠ 6) : 7 = 3 + 4 :=
sorry 

/-
As used below, the `cases` tactic decomposese `h` into its consituents, introducing new assertions
`hp : p` and `hq : q` into the context.

This is our first multi-line tactic proof. Such proofs are enclosed between `begin` and `end`,
rather than following the word `by`.
-/
example (h : p ∧ q) : p :=
begin
  cases h with hp hq,
  exact hp,
end
/-
In standard maths, the above translates to:

  Given the premise `h : p ∧ q`, `p` follows.
  Proof: `h` decomposes into `hp : p` and `hq : q`.
  `p` follows from `hp`.

or, without labelling the premises and assertions:

  Given the premise `p ∧ q`, `p` follows.
  Proof: the premise `p ∧ q` decomposes into assertions `p` and `q`.
  `p` follows from the assertion `p`.

-/



-- There is nothing special about the names `h`, `hp`, or `hq`.
example (bob : p ∧ q) : p :=
begin
  cases bob with jane jill,
  exact jane,
end 

-- As we've seen, we can use `sorry` as a placeholder that Lean expects us to
-- replace later with a term or tactic.

example (h : p ∧ q) : p :=
begin
  cases h with hp hq,
  sorry  
end

example (h : p ∧ q) : p :=
begin 
  cases h with hp hq,
  exact sorry        
end 

-- Replace the `sorry` with a valid term proof or tactic proof in the following examples.
-- As usual, also translate into standard maths.

-- Exercise 012:
example (h : (p ∧ q) ∧ r ) : q :=
begin
  sorry  
end

-- Exercise 013:
-- The next example requires a proof term. It's helpful to note that applications of `.left` or
-- `.right` can be nested.
example (h : (p ∧ q) ∧ r ) : q :=
sorry 
-- Exercise 014:
example (h : p ∧ (q ∧ r) ) : q :=
begin
  sorry  
end

-- Exercise 015:
example (h : p ∧ p) : p :=
begin
  sorry  
end

end and_elimination

/-
SUMMARY:

* And elimination (left and right).
* Tactic blocks using `begin` and `end`.
* The `exact` tactic.
* The `cases` tactic.

-/

end mth1001
