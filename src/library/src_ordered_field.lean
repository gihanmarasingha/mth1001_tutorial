import .src_field_lemmas

namespace mth1001

namespace myreal

class myordered_field (R : Type) extends myfield R :=
(pos : R → Prop)
(decidable_pos : decidable_pred pos)
(trichotomy : ∀ x : R, pos x ∧ ¬x = 0 ∧ ¬pos (-x) ∨ ¬pos x ∧ x = 0 ∧ ¬pos (-x)
  ∨ ¬pos x ∧ x ≠ 0 ∧ pos (-x))
(pos_add_of_pos_of_pos : ∀ x y, pos x → pos y → pos (x+y))
(pos_mul_of_pos_of_pos : ∀ x y, pos x → pos y → pos (x*y))

variables {R : Type} [myordered_field R]

def lt (x y : R) := myordered_field.pos (y-x)

def le (x y : R) := (lt x y) ∨ (x=y)

instance : has_lt R := ⟨lt⟩

instance : has_le R := ⟨le⟩

open_locale classical

noncomputable theory

def max (a b : R) := ite (b ≤ a) a b

def abs (a : R) := max a (-a)

def upper_bound (u : R) (S : set R) := ∀ s ∈ S, s ≤ u

def is_sup (u : R) (S : set R) :=
(upper_bound u S) ∧ (∀ v : R, upper_bound v S → u ≤ v)

def lower_bound (v : R) (S : set R) := ∀ s ∈ S, v ≤ s

def is_inf (u : R) (S : set R) :=
(lower_bound u S) ∧ (∀ v : R, lower_bound v S → v ≤ u)

def minus_set (S : set R) := {x | -x ∈ S}

def bounded_above (S : set R) := ∃ u : R, upper_bound u S

def bounded_below (S : set R) := ∃ v : R, lower_bound v S

def bounded (S : set R) := (bounded_above S) ∧ (bounded_below S)

end myreal

end mth1001