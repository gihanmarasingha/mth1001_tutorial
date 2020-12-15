import .src_13_applications_to_even_and_odd

namespace mth1001

section even_odd_further

/-
We round of this part of the module by proving a further series of results on even and odd numbers.
We begin with a relatively straightforward result.
-/

-- Exercise 093:
example : ∃ m n, odd (m + n) :=
begin 
  sorry    
end

-- Exercise 094:
theorem even_sub_of_even_of_even : ∀ m n, even m → even n → even (m - n) :=
begin 
  sorry    
end

/- 
The next examples require a bit more work. You may wish to review the section on application
to even and odd numbers. Remmember that the `ring` tactic can simplify some algebraic expressions.
-/

-- Exercise 095:
example : ¬(∀ m n, odd (m + n)) :=
begin 
  sorry  
end


-- Exercise 096:
example : ∃ m, ∀ n, even n ∨ even (m + n) :=
begin
  sorry  
end

-- Exercise 097:
example : ∀ m n, even ( (n + m) * (n - m + 1)) :=
begin 
  sorry  
end 

-- Exercise 098:
example : ∀ m, ∃ n, even (m + n) :=
begin
  sorry  
end

-- Exercise 099:
example : ¬(∃ m, ∀ n, even (m + n)) :=
begin
  sorry  
end

end even_odd_further

end mth1001
