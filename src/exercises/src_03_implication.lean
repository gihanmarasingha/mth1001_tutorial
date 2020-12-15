variables p q r : Prop 

namespace mth1001

section implication_elimination

/-
The implication symbol `→` is entered as `\r` or `\to`. The statement `p → q`
has roughly the same meaning as the English phrase, 'if `p`, then `q`'.
-/


/-
Given `h : p → q` and `k : p`, we may deduce `q`. The proof of this is written
in Lean simply as `h k`.
-/
example (hpq : p → q) (hp : p) : q :=
hpq hp 

/-
The same argument can be presented using tactics. The `apply` tactic tries
to match the goal with the conclusion of the supplied argument. If the
argument to `apply` involves additional premises, these are introduced as
new goals.

Here, `q` is the initial goal. The conclusion of `hpq` is `q`, so `apply hpq`
applies and replaces the goal `q` with the new goal `p`.
-/
example (hpq : p → q) (hp : p) : q :=
begin 
  apply hpq,
  exact hp,
end

-- As before, we write the proof term in tactic mode using `exact`.
example (hpq : p → q) (hp : p) : q :=
begin 
  exact hpq hp,
end

-- Exercise 022:
-- We can use subscripts in our names. For example, `h₁` is written `h\1`.
example (h₁ : p ∧ q → r) (h₂ : p) (h₃ : q) : r :=
begin 
  apply h₁,
  sorry  
end

-- Exercise 023:
-- Give a tactic-style proof of the following result.
example (h₁ : p → q) (h₂ : q → r) (h₃ : p) : r :=
begin 
  sorry  
end

-- Exercise 024:
-- Give a term-style proof of the same result.
example (h₁ : p → q) (h₂ : q → r) (h₃ : p) : r :=
have h : q, from 
  sorry,
sorry 

-- Exercise 025:
/-
Once you complete the following example, see if you can write the solution
as a single proof term.
-/
example (a b c d e f : Prop)
        (h₁ : d → a) (h₂ : f → b) (h₃ : e → c) (h₄ : e → a)
        (h₅ : d → e) (h₆ : b → e) (h₇ : c) (h₈ : f) : a :=
begin 
  sorry  
end




end implication_elimination


section implication_introduction 

/-
To 'prove' a statement `p → q` is to assume (or introduce) a proof of `p` and then to derive `q`.
This is called implication introduction.
-/

-- Here is a one-line term-style derivation of `p → q` on the premise `h : q` 
example (h : q) : p → q :=
assume k : p, h

-- We make the proof more readable using `show`
example (h : q) : p → q :=
assume k : p,
show q, from h

-- A similar terminology is used in tactic mode.
example (h : q) : p → q :=
begin
  assume k : p,
  exact h,
end

-- We don't need to specify _what_ we are assuming if we use `intro` instead of `assume`.
-- Lean is clever enough to determine the type of the assumption from the goal.
example (h : q) : p → q :=
begin
  intro k,
  exact h,
end

-- Exercise 026:
/-
In the above examples, we've seen that `p → q` can be deduced on the premise `q`. By
implication, we can derive `q → (p → q)` without any premise!
-/
example : q → (p → q) :=
begin
  assume h₁ : q,
  sorry  
end

-- Exercise 027:
-- You should be able to complete the following example simply by adding one line 
-- at the beginning to your solution to a previous example.
example : p ∧ q → q ∧ p :=
begin
  sorry  
end

end implication_introduction

/-
SUMMARY

* Implication elimination.
* The `apply` tactic for applying an implication.

* Implication introduction 
* Term-style implication introduction using `assume`.
* Tactic-style implication introduction using `intro`.

-/

end mth1001
