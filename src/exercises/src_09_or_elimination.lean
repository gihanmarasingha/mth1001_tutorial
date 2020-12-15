import .src_07_existential_quantification

variables p q r : Prop 

namespace mth1001

section or_elimination

/-
We've seen how to introduce a statement of the form `p ∨ q`. In this section, we'll see
how to _use_ a premise `h : p ∨ q`.

Suppose you have `h : p ∨ q` and you know both
1. `r` follows from `p` and
2. `r` follows from `q`,
then you may derive `r`. This is known as or elimination.
-/

/-
Here's a template for a tactic-mode application of or elimination. The line
  `cases h with hp hq`
decomposes `h` and creates two subgoals:
1. a goal of deriving `r`, where `h` has been replaced with `hp : p` in the context and
2. a goal of deriving `r`, where `h` has been replaced with `hq : q` in the context.

These goals are closed through implication elimination.
-/
example (h : p ∨ q) (k₁ : p → r) (k₂ : q → r) : r :=
begin 
  cases h with hp hq,
  { exact k₁ hp },
  { exact k₂ hq },
end

/-
For a term-style proof, we use the theorem `or.elim`.
-/
#check @or.elim
/-
We see that `or.elim` (ignore the `@` for now) has type
  `∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c`
This means that `or.elim` takes three arguments, one of type `a ∨ b`, one of type `a → c`,
and one of type `b → c`. It returns a proof of `c`.

Recall that the braces in `∀ {a b c : Prop}` tell Lean that the arguments `a`, `b`, and `c` 
are implicit - you need not supply them explicity.
-/

/-
We now use `or.elim` to give a term-style proof of the above result.
-/
example (h : p ∨ q) (k₁ : p → r) (k₂ : q → r) : r :=
or.elim h k₁ k₂

/-
HINT: when constructing a proof term, you can replace arguments with `_`. Even when Lean
cannot infer the argument, it will give you information about the goal and the context.

For instance, replacing `k₂` above with `_` gives the following information:
```
don't know how to synthesize placeholder
context:
p q r : Prop,
h : p ∨ q,
k₁ : p → r,
k₂ : q → r
⊢ q → r
```

The goal is presented as `⊢ q → r`. It's clear that this goal matches exactly the premise `k₂`.
-/

-- Exercise 050:
/-
We can mimic the tactic-mode proof by replacing `k₁` and `k₂` in the proof term
  `or.elim h k₁ k₂`
with more complicated terms. Though inefficient in this case, it provides a useful template
for more sophisticated examples.
-/
example (h : p ∨ q) (k₁ : p → r) (k₂ : q → r) : r :=
or.elim h
( assume hp, k₁ hp )
sorry 

-- Exercise 051:
example (h : (p ∧ q) ∨ (q ∧ r)) : q :=
begin
  cases h with h₁ h₂,
  sorry,
  sorry,
end

-- Exercise 052:
example (h : (p ∧ q) ∨ (q ∧ r)) : q :=
or.elim h
sorry 
sorry 
/-
The combination of the following two results is called right distributivity of `∧` over `∨`
(you don't need to remember this name!)
-/

-- Exercise 053:
theorem or_and_distrib_right1 : (p ∧ r) ∨ (q ∧ r) → (p ∨ q) ∧ r :=
begin 
  intro h,
  cases h with hpr hqr,
  { split,
    { left, exact hpr.left },
    { sorry, } }, 
  { sorry, },
end

-- Exercise 054:
-- See the next example for a hint.
theorem or_and_distrib_right2 : (p ∨ q) ∧ r → (p ∧ r) ∨ (q ∧ r) :=
begin
  sorry  
end

-- If you're stuck with the exercise above, here's a hint:
example : (p ∨ q) ∧ r → (p ∧ r) ∨ (q ∧ r) :=
begin
  intro h,
  cases h with hpq hr,
  cases hpq with hp hq,
  { sorry, },
  { sorry, },
end

/-
We'll present some more examples using `odd` and `even` numbers. You don't need to understand
all the details of the theorem, but it's worth nothing two points

(1) Suppose `h` is an equation or if and only if expression, for example `h : a = b`.
The tactic `rw h` looks for `a` in the goal and replaces it with `b`. However, `rw ←h` looks
for `b` in the goals and replaces it with `a`.

(2) The `linarith` tactic automatically uses any relevant premises in the context to solve linear
equations and inequalities. 

(3) The `ring` tactic simplies algebraic expressions, whether linear or not.
-/
open int 

theorem even_or_odd (m : ℤ) : even m ∨ odd m :=
begin 
  cases (mod_two_eq_zero_or_one m) with h,
  { left,
    use (m/2),
    rw [←(mod_add_div m 2), h],
    ring,
    rw int.mul_div_cancel_left,
    linarith, },
  { right,
    use (m/2),
    rw [←(mod_add_div m 2), h, add_comm],
    congr' 2,
    rw [add_comm, int.add_mul_div_left],
    norm_num,
    linarith, },
end

-- Exercise 055:
-- We use the theorem above in proving the following.
example (b : ℤ) : even b ∨ odd (b + 8) :=
begin 
  cases even_or_odd b with h,
  { sorry, }, 
  { sorry, },  
end 


-- Exercise 056:
theorem even_mul_add_one (a : ℤ) : even (a * (a + 1)) :=
begin
  sorry  
end

end or_elimination

/-
SUMMARY:

* Or elimination.
* Tactic-style elimination using `cases`.
* Term-sytle elimination using `or.elim`.

* Using the `_` placeholder.


-/

end mth1001
