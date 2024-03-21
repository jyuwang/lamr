import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

variable (P Q R S : Prop)

/-
Replace the following sorry's by proofs.
-/

example : (P → Q) ∧ (Q → R) → P → R := by
  intro h hP
  have hPQ := h.1
  have hQR := h.2
  exact hQR (hPQ hP)
  done

example (h : P → Q) (h1 : P ∧ R) : Q ∧ R := by
  have hQ := h h1.1
  exact ⟨hQ, h1.2⟩
  done

example (h : ¬ (P ∧ Q)) : P → ¬ Q := by
  intro hp hq
  have hPQ : P ∧ Q := ⟨hp, hq⟩
  apply h
  exact hPQ
  done

example (h : ¬ (P → Q)) : ¬ Q := by
  intro hq
  have hPQ : P → Q := λ _ => hq
  apply h
  exact hPQ
  done

example (h : P ∧ ¬ Q) : ¬ (P → Q) := by
  intro hPQ -- (P → Q)
  have hP := h.1 -- P
  have hQ := h.2 -- ¬ Q
  apply hQ
  exact (hPQ hP)
  done

example (h1 : P ∨ Q) (h2 : P → R) : R ∨ Q := by
  rcases h1 with hP | hQ
  . left
    exact h2 hP
  . right
    exact hQ
  done

example (h1 : P ∨ Q → R) : (P → R) ∧ (Q → R) := by
  constructor
  . intro hP -- P
    apply h1 -- R
    left
    exact hP
  . intro hQ -- Q
    apply h1 -- R
    right
    exact hQ
  done

example (h1 : P → R) (h2 : Q → R) : P ∨ Q → R := by
  intro hPQ
  rcases hPQ with hp | hq
  . exact h1 hp
  . exact h2 hq
  done

example (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  constructor
  . intro hp
    apply h
    left
    exact hp
  . intro hq
    apply h
    right
    exact hq
  done

-- this one requires classical logic!
example (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q := by
  by_cases hP: P
  . right
    intro hq
    apply h
    exact ⟨hP, hq⟩
  . left
    exact hP
  done

-- this one too
example (h : P → Q) : ¬ P ∨ Q := by
  by_cases hP : P
  . right
    apply h
    exact hP
  . left
    exact hP
  done

/-
Prove the following using only `rw` and the identities given.

Remember that you can use `rw [← h]` to use an identity in the reverse direction,
and you can provides argument to general identities to instantiate them.
-/

#check add_assoc
#check add_comm
#check pow_mul
#check mul_comm
#check mul_add

example (x y z : Nat) : (x + y) + z = (z + y) + x := by
  rw [add_assoc, add_comm, add_comm y z]
  -- x + (y + z) -- add_assoc
  -- (y + z) + x -- add_comm
  -- (z + y) + x -- add_comm

example (x y z : Nat) : (x^y)^z = (x^z)^y := by
  rw [←pow_mul, mul_comm, pow_mul]
  -- x ^ (y * z) -- pow_mul
  -- x ^ (z * y) -- mul_comm
  -- x ^ (z * y) -- pow_mul

example (x y z w : Nat) : (x^y)^(z + w) = x^(y * z + y * w) := by
  rw [←pow_mul, mul_add]
  -- x ^ (y * (z + w)) -- ←pow_mul
  -- x ^ (y * z + y * w) -- mul_add

/-
A *group* is a structure with *, ⁻¹, 1 satisfing the basic group laws.

  https://en.wikipedia.org/wiki/Group_(mathematics)
-/

section
-- Lean lets us declare a group as follows.
variable {G : Type*} [Group G]

#check @mul_left_inv
#check @mul_right_inv
#check @mul_one
#check @one_mul
#check @mul_assoc

example (x y : G) : x * y * y⁻¹ = x := by
  rw [mul_assoc, mul_right_inv, mul_one]

/-
A group is *abelian* if it satisfies the additional law that
`x * y = y * x` for all `x` and `y`.

Fill in the sorry's in the next two theorems. The final one shows that
any group satisfying `x * x = 1` for every `x` is abelian.

You can use `rw [h]` to replace any expression of the form `e * e` by `1`.
-/

theorem fact1 (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = y * (y * z) * (y * z) * z := by
    rw[mul_assoc y (y * z) (y*z), h (y * z), mul_one (y)]
  -- rw [←mul_one y, ←h y, ←mul_one z, ←h z, ←mul_assoc z, ←mul_assoc y, ]
  -- rw [←mul_one y, ←h y, ←mul_one z, ←h z, mul_assoc y, ]
  -- rw [←one_mul y, ]

  -- y * z -- start
  -- y * 1 * z -- ←mul_one y
  -- 1 * y * 1 * z -- ←one_mul y
  -- y⁻¹ * y * y * 1 * z -- ←mul_left_inv y
  -- y⁻¹ * y * y * (y * y) * z -- ←h y
  -- y * (y * y) * z -- ←h y

  -- y * z -- start
  -- y * 1 * z -- ←mul_one y
  -- y * (y * y) * z -- ←h y
  -- y * (y * y) * z * 1 -- ←mul_one z
  -- y * (y * y) * (z * (z * z)) -- ←h z
  -- y * (y * y) * z * (z * z) -- ←mul_assoc
  -- y * (y * y) * z * z * z -- ←mul_assoc
  -- y * y * y * z * z * z -- ←mul_assoc


theorem fact2 (h : ∀ x : G, x * x = 1) (y z : G) :
    z * y = y * (y * z) * (y * z) * z := by
  rw[← mul_assoc, ← mul_assoc, h y, one_mul, mul_assoc, h z, mul_one]
  done




theorem main (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  rw [fact1 h y z, fact2 h y z]

end
