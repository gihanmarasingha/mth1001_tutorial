import tactic.linarith

namespace mth1001

/-
The following is a Lean proof that `10 < 20`.
The line `example : 10 < 20` can be read as, 'Here is a proof of `10 < 20`.

The line `by norm_num` says, 'the result is proved using `norm_num`, a 'tactic'
that can prove many numerical equations and inequalities.

You know the proof is valid because there are no error messages in the
Lean Infoview window and no red wavy text.
-/

example : 10 < 20 :=
by norm_num

/-
In standard mathematical language (henceforth 'standard maths'), the following can be read as

  `6 ≥ 2` follows using known numerical equations or inequalities.

Note: `≥` is written `\ge`. Can you guess how to write `≤`?
-/
example : 6 ≥ 2 := by norm_num


/-
Write the following in standard maths. Note: `≠` is written `\ne`.
-/
example : 15 ≠ 10 :=
by norm_num

-- Play around with this. Come up with your own examples similar to those above.
-- See what happens if you try to use `norm_num` to prove something false, like `1 = 0`.

/-
Let's make things interesting by introducing variables. Here, `ℤ` is the 'type' of integers and is 
written `\Z`. The following command introduces variables `x` and `y` of type `ℤ`.
-/

variables (x y : ℤ)

/-
The `linarith` tactic can prove many equations and inequalities involving
variables. The standard maths tranlation of the following proof is:

  For every integer `x`, `x ≥ x` follows using known linear equations and inequalities.

-/
example : x ≥ x :=
by linarith

/-
We can suppress error messages by writing `sorry` where Lean expects a proof.
Lean warns us that the proof is not complete with a yellow wavy line and /or a warning message
in the Infoview window.
-/

-- Exercise 001:
-- Replace `sorry` with `by linarith` in the following example. Write the example in standard maths.
example : y + 5 ≥ y + 3 :=
sorry 

/-
`linarith` can only handle _linear_ equations and inequalities --- those involving no quadratic or
higher-order terms. The `ring` tactic can simplify many other algebraic expressions.

The following states (in standard maths):

  For every integer `y`, `(y + 2)^2 = y^2 + 4*y + 4` follows by algebra.

Note: `^` represent exponentiation. Do not confuse it with `∧`, which you'll see later.
-/
example : (y + 2)^2 = y^2 + 4*y + 4 :=
by ring


/-
Some of the claims in the next few examples are true while others are false!
Determine, by hand, which are which. Test your guesses by using either the
`linarith` or the `ring` tactic to replace the sorry.

For each true statement, write out the example in standard maths.
-/

-- Exercise 002:
-- Is the following true or false?
example : (x + y)^2 = x^2 + y^2 :=
sorry

-- Exercise 003:
-- Is the following true or false?
example : (x - y) * (x + y) = x^2 - y^2 :=
sorry 

-- Exercise 004:
-- Is the following true or false?
example : 3 * x + 8 ≥ 5 * x :=
sorry 

/-
The previous example may cause some confusion. This isn't a question of *finding* the values of `x`
for which the equality `3 * x + 8 ≥ 5 * x` is true. Rather the problem is, 'Can you
prove, *for every* value of `x`, that `3 * x + 8 ≥ 5 * x`? If so, give a proof!'.
-/

/-
Of course, there *are* values of `x` for which the inequality holds. You can
easily that the inequality holds if `x ≤ 4`. In Lean, we write `h : x ≤ 4`
to mean, 'let `h` denote the premise (or assumption or hypothesis) that `x ≤ 4`'.

There's nothing special about `h`, we could instead write `k : x ≤ 4`,
`jane : x ≤ 4`, or `hal9000 : x ≤ 4`.
-/

/-
In English, we write the result below as, 'Given the premise `k : x ≤ 4`, the
inequality `3 * x + 8 ≥ 5 * x` follows'.

In normal mathematical writing, we do not label premises. Thus, we could write,
'Given `x ≤ 4`, the inequality `3 * x + 8 ≥ 5 * x` follows'.
-/

example (k : x ≤ 4) : 3 * x + 8 ≥ 5 * x :=
by linarith

/-
If `x ≤ 0`, then also `x ≤ 4`, so we should expect to get the conclusion of the above example from
this new premise.
-/

example (k : x ≤ 0) : 3 * x  + 8 ≥ 5 * x :=
by linarith

/-
More generally, the result is true with any stronger premise. That is, suppose we assert
`k₁ : x ≤ y` together with  `k₂ : y ≤ 4`. It then follows that `x ≤ 4` and we recover the result.

Here, we type `k\1` for `k₁`.
-/ 

example (k₁ : x ≤ y) (k₂ : y ≤ 4) : 3 * x + 8 ≥ 5 * x :=
by linarith

/-
What's special about `4` is that it's the *largest* integer with this property. We'll consider
how to formalise this notion in a later section.
-/

-- Exercise 005:
/- Complete the following statement and proof. Ensure you fill in the first `sorry` with
the *smallest* integer value that works.
-/
example (h : x ≥ sorry) : 9 * x + 6 ≥ 2 * x + 20 := 
sorry 

-- Exercise 006:
/- Complete the following statement and proof. Fill in the first `sorry` with the *largest*
integer value that works. Can you prove (by hand) *why* this is the largest value?
-/
example (h₁ : -3 * x + 2 * y ≤ 2 ) (h₂ : 5 * x + y ≥ sorry): x ≥ 6 := 
sorry 

/-
SUMMARY:

In this file, you have learned about:

* Statements of results in Lean, in the form `example premise₁ … premiseₙ : conclusion`.
* Translating between Lean and standard maths.
* The idea of a premise, also known as a hypothesis or assumption. Lean notation for premises.
* One-line tactic-style proofs, using `by`.
* Variables in Lean, using `variables`.
* The `norm_num` tactic for proving numerical equations and inequalities.
* The `linarith` tactic for proving linear equations and inequalities (involving variables).
* The `ring` tactic for simplifying more general equations.
* Writing subscripts in Lean.
-/

end mth1001
