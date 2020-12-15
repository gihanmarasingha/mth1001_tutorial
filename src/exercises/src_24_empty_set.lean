import data.set

open set

namespace mth1001

section emtpy_set

variable A : Type*

/-
In this very short file, we show that for every set `S`, the empty set is a subset of `S`.
-/

example (S : set A) : ∅ ⊆ S :=
begin
  intro x, -- Assume `x : A`. The goal is to prove `x ∈ ∅ → x ∈ S`.
  intro h, -- Assume `h : x ∈ ∅`.
  exfalso, -- By false introduction, it suffices to prove `⊥`,
  apply h, -- which follows from `h`.
end

end emtpy_set

end mth1001
