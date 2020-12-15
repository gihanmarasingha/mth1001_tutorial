import .src_ordered_field

namespace mth1001

namespace myreal

class myreal_field (R : Type) extends myordered_field R :=
(nan : R)
(completeness : ∀ {S : set R}, S ≠ ∅ → (∃ u : R, upper_bound u S) → ∃ v : R, is_sup v S)

variables {R : Type} [myreal_field R]

open classical myreal_field

local attribute [instance] prop_decidable

noncomputable def sup (S : set R) := if h : ∃ x, is_sup x S then some h else nan

noncomputable def inf (S : set R) := if h : ∃ x, is_inf x S then some h else nan

end myreal

end mth1001