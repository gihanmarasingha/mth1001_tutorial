namespace mth1001

namespace myreal

section comm_group

class comm_group (R : Type) extends has_add R, has_zero R, has_neg R :=
(add_comm : ∀ a b : R, a + b = b + a)
(add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c))
(add_zero : ∀ a : R, a + 0 = a)
(add_inv : ∀ a : R, a + (-a) = 0)

variables {R : Type} [comm_group R]

def sub (x y : R) := x + (-y)

instance : has_sub R := ⟨sub⟩

end comm_group

class myfield (R : Type) extends comm_group R, has_one R, has_mul R, has_inv R :=
(mul_comm : ∀ a b : R, a * b = b * a)
(mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c))
(mul_one : ∀ a : R, a * 1 = a)
(mul_inv : ∀ a : R, a ≠ 0 → a * a⁻¹ = 1)
(mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
(zero_ne_one : (0 : R) ≠ (1 : R))

variables {R : Type} [myfield R]

def of_nat : ℕ → R
| 0            := (0 : R)
| (nat.succ x) := (of_nat x) + 1

instance : has_coe ℕ R := ⟨of_nat⟩

lemma coe_nat_succ (n : ℕ) : ((nat.succ n) : R) = (n : R) + (1 : R) := rfl

end myreal

end mth1001
