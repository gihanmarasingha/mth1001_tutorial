import .src_04_theorems

variables p q r : Prop 

namespace mth1001

section if_and_only_if

/-
The symbol `↔`, written `\iff` is read 'if and only if'. From `p ↔ q`, one can deduce `p → q` and
`p → q`. Likewise, from `p → q` and `q → p`, one can deduce `p ↔ q`.

Given propositions `p` and `q`, if `p ↔ q`, we say that `p` is _equivalent_ to `q`.
-/

-- Here is a term-style derivation of `p ↔ q` from `h₁ : p → q` and `h₂ : q → p`. 
example (h₁ : p → q) (h₂ : q → p) : p ↔ q :=
iff.intro h₁ h₂ 

/-
Equally, we can use the `split` tactic to decompose the goal `p ↔ q` into two goals: one
to prove `p → q` and the other to prove `q → p`.
-/
example (h₁ : p → q) (h₂ : q → p) : p ↔ q :=
begin 
  split,
  { exact h₁, },
  { exact h₂, },
end

-- Exercise 033:
-- We combine the previous results `and_assoc` and `and_assoc2`. 
theorem and_assoc : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin 
  split,
  { sorry}, 
  { sorry, }, 
end 


/-
Below is a tactic mode proof of `p → q` from `h : p ↔ q`. Note how `cases` is used to decompose
the premise `h` into two new premises, `hpq : p → q` and `hqp : q → p`.
-/
example (h : p ↔ q) : p → q :=
begin 
  cases h with hpq hqp,
  exact hpq,
end 

-- Exercise 034:
example (h : p ↔ q) : q → p :=
begin 
  sorry  
end 

/-
Alternatively, we can give a term-style proof. If `h : p ↔ q`, then `h.mp` is a proof of `p → q`
and `h.mpr` is a proof of `q → p`. Here `mp` is an abbreviation of 'modus ponens', the Latin name
for implication elimination.
-/

example (h : p ↔ q) : p → q :=
h.mp

example (h : p ↔ q) : q → p :=
h.mpr

-- Exercise 035:
-- We prove `p ∧ q ↔ q ∧ p` using the theorem `and_of_and` from the previous section.
theorem and_iff_and : p ∧ q ↔ q ∧ p :=
begin 
  split, 
  { exact and_of_and p q },
  { sorry, }, 
end 

end if_and_only_if

/-
SUMMARY:

* Iff introduction.
* Term-style introduction using `iff.intro`.
* Tactic-style introduction using `split`.

* Iff elimination.
* Tactic-style elimination using `cases`.
* Term-style elimination using `.mp` or `.mpr`.
-/

end mth1001
