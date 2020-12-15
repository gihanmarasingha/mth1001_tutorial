import data.rat

open function

namespace mth1001

section composite

def q₁ (x : ℕ) : ℤ := x + 3
def q₂ (x : ℤ) : ℚ := 2 * x

/-
When a function `f` takes values from a type (or set) `α` and returns values in a type (or set) `β`,
we write that the *domain* of `f` is `α` and the *codomain* of `f` is `β`. This is denoted
`f : α → β`.
-/

/-
Given `f : α → β` and `g : β → γ`, the *composite* of `g` and `f`, denoted `g ∘ f` is the function
`g ∘ f : α → γ` with the property that `(g ∘ f) x = g (f x)`, for every `x : α`.
-/


-- With `q₁` and `q₂` as above, `q₁ : ℕ → ℤ` and `q₂ : Z → ℚ`. So `q₂ ∘ q₁ : ℕ → ℚ`.
#check q₁
#check q₂
#check q₂ ∘ q₁

-- We verify, that `(q₂ ∘ q₁) 5 = q₂ (q₁ 5)`.
#eval (q₂ ∘ q₁) 5
#eval q₂ (q₁ 5)

/-
With the above functions, `q₁ ∘ q₂` is *not defined* as the codomain of `q₂` differs from the
domain of `q₁`.
-/

/-
If all the domains and codomains of two functions, say `p₁` and `p₂` are equal, then it makes sense
to consider both composites. However, `p₂ ∘ p₁` will not (in general) be equal to `p₁ ∘ p₂`.
-/

def p₁ (x : ℤ) : ℤ := 3 * x
def p₂ (y : ℤ) : ℤ := y + 4

#eval (p₂ ∘ p₁) 6  -- `(p₂ ∘ p₁) 6 = p₂ (p₁ 6) = p₂ (3*6) = p₂ 18 = 18 + 4 = 22`, but
#eval (p₁ ∘ p₂) 6  -- `(p₁ ∘ p₂) 6 = p₁ (p₂ 6) = p₁ (6 + 4) = p₁ 10 = 3 * 10 = 30`.


/-
We'll prove that the composite of two injective functions is injective.
-/

variable {α : Type*}
variable {β : Type*}
variable {γ : Type*}

theorem injective_comp {f : α → β} {g : β → γ} (h₁ : injective f) (h₂ : injective g) :
  injective (g ∘ f) :=
begin
  unfold injective at *, -- We use the definition of injective.
  intros a₁ a₂ h, -- Assume `a₁ a₂ : α`. Assume `h : (g ∘ f) a₁ = (g ∘ f) a₂`.
  have h₄ : f a₁ = f a₂,
    from h₂ h, -- By injectivity of `g`, applied to `h`, we have `h₄ : f a₁ = f a₂`.
  show a₁ = a₂, from h₁ h₄, -- We show `a₁ = a₂` by injectivity of `f`, applied to `h₄`.
end


/-
We'll prove that the composite of two surjective functions is surjective. The proof is
more involved that the corresponding injectivity result.
-/
theorem surjective_comp {f : α → β} {g : β → γ} (h₁ : surjective f) (h₂ : surjective g) :
  surjective (g ∘ f) :=
begin
  unfold surjective at *, -- We use the definition of surjective.
  intro c, -- Assume `c : γ`. It suffices to show `∃ a : α, (g ∘ f) a = c`.
  sorry  
end

-- Exercise 145:
-- From these two results, we have that the composite of two bijective functions is bijective.
theorem bijective_comp {f : α → β} {g : β → γ} (h₁ : bijective f) (h₂ : bijective g) :
  bijective (g ∘ f) :=
begin
  sorry  
end

end composite

end mth1001
