namespace mth1001

class comm_group (R : Type) extends has_add R, has_zero R, has_neg R :=
(add_comm : ∀ a b : R, a + b = b + a)
(add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c))
(add_zero : ∀ a : R, a + 0 = a)
(add_inv : ∀ a : R, a + (-a) = 0)

class myfield (R : Type) extends comm_group R, has_one R, has_mul R, has_inv R :=
(mul_comm : ∀ a b : R, a * b = b * a)
(mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c))
(mul_one : ∀ a : R, a * 1 = a)
(mul_inv : ∀ a : R, a ≠ 0 → a * a⁻¹ = 1)
(mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
(zero_ne_one : (0 : R) ≠ (1 : R))

end mth1001
