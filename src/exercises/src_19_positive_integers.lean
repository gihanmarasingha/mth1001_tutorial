import data.num.basic 
set_option pp.structure_projections false

namespace mth1001

/-
In this file, we set up a type for the positive integers and prove theorems about it.
-/

section setup 

  -- You can ignore the material in this section. It's needed to set up
  -- the type of positive integers and to define addition.
  @[derive has_reflect, derive decidable_eq]
  inductive pint : Type
  | unus  : pint
  | heir : pint → pint

  open pint

  def add : pint → pint → pint
  | a   unus        := heir a                --     a + unus = heir a
  | a   (heir b)    := heir (add a b)        -- a + (heir b) = heir (a + b)

  notation a `+` b := add a b

end setup

section addition

open pint 

/-
`unus` is our name for 'one'. There are two defining rules for addition.attribute

1. `add_unus`. For every positive integer `a`, we have `a + unus a = heir a`, where
   `heir a` is the 'heir' of `a` (like the successor of `a` in our notes).

2.  `add_heir`. For positive integers `a` and `b`, we have `a + heir b = heir (a+b)`.
-/
lemma add_unus  (a : pint) : a + unus = heir a := rfl
lemma add_heir (a b : pint) : a + heir b = heir (a + b) := rfl

/-
 In this example, we prove `unus + a = heir a`, for every positive
 integer `a`. You do this by induction on `a`.
-/
lemma unus_add (a : pint) :  unus + a = heir a:=
begin 
  induction a with k hk,
  { rw add_unus }, -- The base case is to prove the result holds when `a` is `unus`.
  { rw add_heir,   -- This is the inductive step.
    rw hk, },
end 

-- Exercise 109:
/-
Note that multiple applications of `rw h` (for some lemma or equation `h`)
can be replaced with `repeat {rw h}`.
-/
lemma add_assoc (a b c : pint) : (a + b) + c = a + (b + c) :=
begin 
  induction c with k hk,
  { sorry, }, 
  { sorry, }, 
end 

-- Exercise 110:
lemma heir_add (a b : pint) : (heir a) + b = heir (a + b) :=
begin
  sorry  
end

-- Exercise 111:
-- We can now prove commutativity of addition.
lemma add_comm (a b : pint) : a + b = b + a :=
begin
  sorry  
end 

end addition

section setup
  -- You can ignore the material in this section. It's needed to define multiplication.

  open pint 

  inductive less_than_or_equal (a : pint) : pint → Prop
  | refl : less_than_or_equal a
  | step : Π {b}, less_than_or_equal b → less_than_or_equal (heir b)

  def mul : pint → pint → pint
  | a   unus      := a
  | a   (heir b)  := (mul a b) + a 

  notation a `*` b := mul a b 

end setup

section multiplication

open pint 

-- The rules we'll use in working with multiplication are `mul_unus` and `mul_heir`.
lemma mul_unus (a : pint) : a * unus = a := rfl
lemma mul_heir (a b : pint) : a * (heir b) = (a * b) + a := rfl

-- Exercise 112:
lemma unus_mul (a : pint) : unus * a = a :=
begin
  sorry  
end

-- Exercise 113:
lemma heir_mul (a b : pint) : (heir a) * b = a * b + b :=
begin 
  sorry  
end

-- Exercise 114:
-- We can now prove commutativity of multiplication.
lemma mul_comm (a b : pint) : a * b = b * a :=
begin 
  sorry  
end 

/-
In the remainder of this section, we prove associativity of multiplication.
-/

-- Exercise 115:
lemma mul_add (a b c : pint) : a * (b + c) = a * b + a * c :=
begin
  sorry  
end

-- Exercise 116:
-- Associativity of multiplication.
lemma mul_assoc (a b c : pint) : (a * b) * c = a * (b * c) :=
begin
  sorry  
end

end multiplication

end mth1001
