variables p q r : Prop 

namespace mth1001

section and_introduction

/-
In the previous section, we saw how to eliminate `∧`. That is, we saw how to take a premise
involving `∧` and derive a statement in which that occurrence of `∧` has been removed.

In this section, we do the opposite. We introduce `∧`.
-/

/-
The following can be read in standard maths as:

  Given `hp : p` and `hq : q`, `p ∧ q` follows by and introduction on `hp` and `hq`.

or:

  Given `p` and `q`, `p ∧ q` follows by and introduction on `p` and `q`.
-/
example (hp : p) (hq : q) : p ∧ q :=
and.intro hp hq

-- Below, the symbols `⟨` and `⟩` are entered as `\<` and `\>`.
example (hp : p) (hq : q) : p ∧ q :=
⟨hp, hq⟩

/-
Below, the `split` tactic decoposes the goal `p ∧ q` into two subgoals, `p`
and `q`. Compare this with the `cases` tactic that decomposes the premise.

We wrote write this in standard maths as:

  Given `hp : p` and `hq : q`, `p ∧ q` follows.
  Proof: It suffices to prove both `p` and `q`.
  `p` follows from `hp`.
  `q` follows from `hq`.

or:

  Given `p` and `q`, `p ∧ q` follows.
  Proof: It suffices to prove both `p` and `q`.
  `p` follows from `p`.
  `q` follows from `q`.
-/
example (hp : p) (hq : q) : p ∧ q :=
begin 
  split,
    exact hp,
    exact hq,
end

-- It is considered good style to wrap braces around each new subgoal.
example (hp : p) (hq : q) : p ∧ q :=
begin 
  split,
  { exact hp, },
  { exact hq, },
end

-- We can even combine tactic-style and term-style proofs.
example (hp : p) (hq : q) : p ∧ q :=
by exact and.intro hp hq

-- Exercise 016:
-- Use both `cases` and `split` to complete the following proof. Either write in Lean and convert
-- into standard maths or the other way round.
-- There isn't only one correct solution. Find as many essentially different solutions as you can.
example (h : p ∧ q) : q ∧ p :=
begin
  sorry  
end

-- Exercise 017:
-- This time, use `cases`, but complete the proof using `and.intro` or `⟨` and `⟩`
example (h : p ∧ q) : q ∧ p :=
begin
  sorry  
end

-- Exercise 018:
-- Give a one-line proof term.
example (h : p ∧ q) : q ∧ p :=
sorry 

-- We'll prove one direction of associativity of `∧`. First using tactics. 
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := 
begin 
  cases h with hp hqr,
  cases hqr with hq hr,
  split,
  { split,
    { exact hp, },
    { exact hq, }},
  { exact hr, },
end

-- Now as a purely term-style proof. Not very readable!
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := 
⟨ ⟨h.1, h.2.1 ⟩, h.2.2 ⟩ 

-- To aid readability, we can introduce statements into the context using `have`.
-- In tactic mode, the `have` tactic must be followed by a tactic that closes the goal.
example (h : p ∧ q) : q ∧ p :=
begin 
  have hp : p,
  { exact h.left, },
  have hq : q, 
  { exact h.right, },
  exact ⟨hq, hp⟩, -- Here, `⟨hq, hp⟩` is a abbreviation of `and.intro hq hp`.
end

-- In a term-style proof, we use `have` … `from`.
example (h : p ∧ q) : q ∧ p :=
have hp : p, from h.left,
have hq : q, from h.right,
⟨hq, hp⟩

-- We can emulate the term-style `have` … `from` in tactic mode using either 
example (h : p ∧ q) : q ∧ p :=
begin 
  have hp : p, from h.left,
  have hq : q := h.right,
  exact and.intro hq hp, -- I could have written `⟨hq, hp⟩` instead of `and.intro hq hp`.
end

-- Exercise 019:
-- Fill in the `sorry`s below to give a proof of the goal introduced by the `have` tactic.
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
begin
  cases h with hp hqr,
  have hpq : p ∧ q, -- Follow `have` by a tactic that closes the goal `p ∧ q`.
  { split,
    { sorry, }, 
    { sorry, }, }, 
  have hr : r, from -- `have` … `from` should be followed by a proof term for the goal `r`.
    sorry,
  exact ⟨hpq, hr⟩,
end

-- Exercise 020:
-- Complete the following term-style proof of the above result.
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := 
have hp : p, from sorry, 
have hqr : q ∧ r, from h.2,
have hpq : p ∧ q, from sorry, 
have hr : r, from hqr.2,
⟨hpq, hr⟩

-- To further aid readability, `show` … `from` indicates what we are proving.
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := 
have hp : p, from sorry, 
have hqr : q ∧ r, from h.2,
have hpq : p ∧ q, from sorry, 
have hr : r, from hqr.2,
show (p ∧ q) ∧ r, from ⟨hpq, hr⟩


-- Exercise 021:
/-
Prove the other direction of associativity of `∧`. Choose whatever proof style you like.
Add `begin` and `end` if you want to use a tactic-style proof.
-/
example (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
sorry 

end and_introduction

/-
SUMMARY

* And introduction.
* Term-style proof using `and.intro` or `⟨` and `⟩`.
* Tactic-sytyle and introduction using `split`.
* Proving intermediate steps with `have`.
* Using `show` to indicate what is being proved. 
-/

end mth1001
