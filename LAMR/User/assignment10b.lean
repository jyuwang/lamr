import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
Replace each `sorry` by a proof. The examples from lecture will be helpful.

Each problem is worth 1 point.
-/

open Function

section

variable {α β : Type} (p q : α → Prop) (r : α → β → Prop)

example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x := by
  intro h
  intro x
  constructor
  . exact h.left x
  . exact h.right x
  done

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  intro x
  rcases h with h1 | h2
  case inl =>
    left
    exact h1 x
  case inr =>
    right
    exact h2 x
  done

example : (∃ x, p x ∧ q x) → ∃ x, p x := by
  intro h
  rcases h with ⟨x, hpq⟩
  exact ⟨x, hpq.left⟩
  done

example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y := by
  intro h
  intro y
  rcases h with ⟨x, h⟩
  exact ⟨x, h y⟩
  done

end

section
open Function

#check Injective
#check Surjective

variable (f : α → β) (g : β → γ)

example (injgf : Injective (g ∘ f)) :
    Injective f := by
  intro x₁ x₂ h
  apply injgf
  have h' : g (f x₁) = g (f x₂) := by rw [h]
  exact h'
  done

-- this one is worth two points
example (surjgf : Surjective (g ∘ f)) (injg : Injective g) :
    Surjective f := by
  intro y
  obtain ⟨a, ha⟩ : ∃ a, g (f a) = g y
  apply surjgf (g y)
  use a
  apply injg
  exact ha
  done

end
