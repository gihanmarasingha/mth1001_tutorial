import data.num.basic 
set_option pp.structure_projections false

namespace mth1001

section setup 

@[derive has_reflect, derive decidable_eq]
inductive mynat : Type
| zero  : mynat
| S : mynat → mynat

open mynat

def add : mynat → mynat → mynat
| a   zero        := a                --     a + zero = a
| a   (S b)    := S (add a b)        -- a + (S b) = S (a + b)

notation a `+` b := add a b

end setup

section addition

open mynat 

lemma add_zero  (a : mynat) : a + zero = a := rfl
lemma add_S (a b : mynat) : a + S b = S (a + b) := rfl

-- Exercise 117:
lemma zero_add (a : mynat) :  zero + a = a:=
begin 
  induction a with k hk,
  { sorry, }, 
  { sorry, }, 
end 

-- Exercise 118:
/-
Note that multiple applications of `rw h` (for some lemma or equation `h`)
can be replaced with `repeat {rw h}`.
-/
lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin 
  induction c with k hk,
  { sorry, }, 
  { sorry, }, 
end

-- Exercise 119:
lemma S_add (a b : mynat) : (S a) + b = S (a + b) :=
begin
  sorry  
end

-- Exercise 120:
lemma S_eq_add_one (a : mynat) : S a = a + S zero :=
begin
  sorry  
end

-- Exercise 121:
lemma add_comm (a b : mynat) : a + b = b + a :=
begin
  sorry  
end 

end addition 

section multiplication

open mynat 

-- Next result adapted from data/nat/basic.lean
inductive less_than_or_equal (a : mynat) : mynat → Prop
| refl : less_than_or_equal a
| step : Π {b}, less_than_or_equal b → less_than_or_equal (S b)

def mul : mynat → mynat → mynat
| a   zero      := zero
| a   (S b)  := (mul a b) + a 

notation a `*` b := mul a b 

open mynat

lemma mul_zero (a : mynat) : a * zero = zero := rfl
lemma mul_S (a b : mynat) : a * (S b) = (a * b) + a := rfl

-- Exercise 122:
lemma zero_mul (a : mynat) : zero * a = zero :=
begin
  sorry  
end

-- Exercise 123:
lemma S_mul (a b : mynat) : (S a) * b = a * b + b :=
begin 
  sorry  
end

-- Exercise 124:
lemma mul_comm (a b : mynat) : a * b = b * a :=
begin 
  sorry  
end 

/-
In the remainder of this section, we prove associativity of multiplication.
-/

-- Exercise 125:
lemma mul_add (a b c : mynat) : a * (b + c) = a * b + a * c :=
begin
  sorry  
end

-- Exercise 126:
lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin
  sorry  
end

end multiplication

end mth1001
