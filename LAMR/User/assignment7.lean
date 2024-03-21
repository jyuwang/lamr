import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import LAMR.Examples.implementing_first_order_logic.TarskisWorld

/-
Each proof is worth 1.5 points.
-/

/-
Problem 1. (3 points)

Rewriting propositions. Note that `rw` can be used with `h : P ↔ Q` as well as with
`h' : P = Q`.

Replace each `sorry` by a proof, using some of the identities below. Note that you
did these exercises by hand on an earlier assignment.
-/

#check not_and_self_iff
#check and_not_self_iff
#check and_comm
#check and_assoc
#check and_or_left
#check and_or_right
#check or_and_right
#check or_and_left
#check or_comm
#check or_assoc
#check not_or
#check or_false
#check or_true
#check false_or
#check true_or
#check or_self
#check and_false
#check and_true
#check false_and
#check true_and
#check and_self
#check not_not
#check not_false
#check not_true
#check imp_iff_not_or

-- 1A. Prove this.
example (P Q : Prop) : ((P → Q) ∧ P) ↔ (P ∧ Q) := by
  rw [imp_iff_not_or, and_comm, and_or_left, and_not_self_iff, false_or]

-- 1B. Prove this.
example (P Q : Prop) : ((P → Q) ∨ ¬ P) ↔ (P → Q) := by
  rw [imp_iff_not_or, or_assoc, or_comm, or_assoc, or_self, or_comm, ←imp_iff_not_or]


/-
Problem 2 (6 points).

Give *proof terms* for the following lemmas, using the theorems below.
The curly brackets mean that the arguments are implicit, i.e. you do not enter them.
-/

section
variable (P Q R : Prop)

#check And.intro
#check And.left
#check And.right
#check Or.inl
#check Or.inr

-- Also:
-- function abstraction (for proving `A → B`)
-- function application (i.e. applying `h : A → B` to `h1 : A` to get `h h1 : B`)
-- match for disjunction

-- 2A. Prove this.
example : P ∧ Q → P ∨ R :=
  fun h1 => Or.inl (And.left h1)

-- 2B. Prove this.
example (h : P → Q → R) : P ∧ Q → R :=
  fun h1 => h (And.left h1) (And.right h1)

-- 2C. Prove this.
example (h : P ∧ Q → R) : P → Q → R :=
  fun hp hq => h (And.intro hp hq)

-- 2D. Prove this.
example (h : P ∨ Q) : (P → R) → (Q → R) → R :=
  fun hpr => fun hqr => match h with
    | Or.inl hp => hpr hp
    | Or.inr hq => hqr hq

end


/-
Problem 3 (7.5 points).

Induction on the natural numbers.

Replace each `sorry` by a proof.
-/

-- example induction proofs from the textbook
def sum_up_to : Nat → Nat
  | 0 => 0
  | (n + 1) => (n + 1) + sum_up_to n

example (n : Nat) : 2 * sum_up_to n = n * (n + 1) := by
  induction n with
  | zero =>
      rw [Nat.zero_eq, sum_up_to]
  | succ n ih =>
      rw [Nat.succ_eq_add_one, sum_up_to, mul_add, ih]
      ring

def sum_odds : Nat → Nat
  | 0 => 0
  | (n + 1) => (2 * n + 1) + sum_odds n

theorem sum_odds_eq_square (n : Nat) : sum_odds n = n^2 := by
  induction n with
  | zero =>
      rw [sum_odds, Nat.zero_eq, pow_two, zero_mul]
  | succ n ih =>
      rw [sum_odds, ih, Nat.succ_eq_add_one]
      ring

-- you can use these theorems:
#check Nat.add_zero
#check Nat.add_succ
#check Nat.add_assoc

def mul' : Nat → Nat → Nat
  | _, 0 => 0
  | m, (n + 1) => mul' m n + m

-- 3A. Prove this.
theorem mul'_add (m n k : Nat) : mul' m (n + k) = mul' m n + mul' m k := by
  induction n with
  | zero =>
      rw [Nat.zero_eq, mul', Nat.zero_add, Nat.zero_add]
  | succ n ih =>
      rw [Nat.succ_eq_add_one, mul', Nat.add_comm n 1, Nat.add_assoc, Nat.add_comm, mul', ih]
      ring

-- 3B. Prove this.
theorem mul'_assoc (m n k : Nat) : mul' (mul' m n) k = mul' m (mul' n k) := by
  induction k with
  | zero =>
      rw [Nat.zero_eq, mul', mul', mul']
  | succ k ih =>
      rw [mul', mul', mul'_add, ih]

-- 3C. Prove this.
theorem zero_mul' (m : Nat) : mul' 0 m = 0 := by
  induction m with
  | zero =>
      rw [Nat.zero_eq, mul']
  | succ m ih =>
      rw [Nat.succ_eq_add_one, mul', ih, Nat.add_zero]

theorem aux (m n : Nat) : m + Nat.succ n = n + Nat.succ m := by
  rw [Nat.add_succ, Nat.add_succ, Nat.add_comm]

-- 3D. Prove this.
theorem succ_mul' (m n : Nat) : mul' (Nat.succ m) n = mul' m n + n := by
  induction n with
  | zero => rw [mul', mul', Nat.zero_add]
  | succ n ih => rw [mul', mul', ih, Nat.add_assoc, aux n m, ←Nat.add_assoc]

-- 3E. Prove this.
theorem mul'_comm (m n : Nat) : mul' m n = mul' n m := by
  induction n with
  | zero => rw [mul', zero_mul']
  | succ n ih => rw [mul', ih, succ_mul']


/-
Problem 4 (7.5 points).

Induction on lists.

Replace the following `sorry`s by proofs.
-/

section
open List

-- You can use `rw [map]` to expand the definiton of map:
example (f : α → β) : map f [] = [] := by
  rw [map]

example (f : α → β) (x : α) (xs : List α) : map f (x :: xs) = f x :: map f xs := by
  rw [map]

-- 4A. Prove this.
example (f : α → β) (xs : List α) : map f (tail xs) = tail (map f xs) := by
  induction xs with
  | nil => rw [map, tail, map, tail]
  | cons x xs _ => rw [map, tail, tail]

-- returns `none` if the list if empty
#check head?
#check head?_nil
#check head?_cons

#check Option.map
#check Option.map_none'
#check Option.map_some'

example : head? ([] : List Nat) = none := by
  rw [head?_nil]

example : head? ([1, 2, 3] : List Nat) = some 1 := by
  rw [head?_cons]

example (f : α → β) : Option.map f none = none := by
  rw [Option.map_none']

example (f : α → β) (a : α) : Option.map f (some a) = some (f a) := by
  rw [Option.map_some']

-- 4B. Prove this.
example (f : α → β) (xs : List α) : Option.map f (head? xs) = head? (map f xs) := by
  induction xs with
  | nil => rw [head?, map, head?, Option.map_none']
  | cons x xs _ => rw [head?, map, head?, Option.map_some']

/-- `snoc` is the mirror image of `cons`. -/
def snoc : List α → α → List α
  | [], y => [y]
  | (x :: xs), y => x :: snoc xs y

-- You use these:
#check nil_append
#check cons_append

-- Also: note that `[y]` is notation for `y :: nil`.
-- Step through the rewrites to see what is going on.
example (f : α → β) : map f [y] = [f y] := by
  rw [map, map]

-- 4C. Prove this.
theorem snoc_eq_append (xs : List α) (y : α) : snoc xs y = xs ++ [y] := by
  induction xs with
  | nil => rw [snoc, nil_append]
  | cons x xs ih => rw [snoc, cons_append, ih]

-- 4D. Prove this by induction.
theorem map_snoc (f : α → β) (xs : List α) (y : α) : map f (snoc xs y) = snoc (map f xs) (f y) := by
  induction xs with
  | nil => rw [snoc, map, snoc, map, map]
  | cons x xs ih => rw [snoc, map, map, snoc, ih]

#check map_append

-- 4E. Prove it again without induction, using `snoc_eq_apppend` and `map_append`.
theorem map_snoc' (f : α → β) (xs : List α) (y : α) : map f (snoc xs y) = snoc (map f xs) (f y) := by
  induction xs with
  | nil => rw [snoc, map, snoc, map, map]
  | cons x xs ih => rw [snoc, map, map, snoc, ih]

-- TODO: w/o induction

/-
Problem 5 (3 + 3 = 6 Points).

Tarski's World.

If you pull the current version of the repository, you can uncomment the lines
that begin with `#3d_world` and put your cursor on that token to see a nicer
rendering of the worlds you create.
-/
open Shape
open Size

/-
5A.

Create a world with at most three objects in which all the following sentences are true.
-/

def ockham : World := [
  -- add objects here
]

-- Tip: You can pin this display open using the 📌 icon in the Lean Infoview
#eval ockham.show
-- #3d_world ockham

#eval ockham.eval fo!{∀ x. ∀ y. (SameRow(%x, %y) ∧ SameCol(%x, %y)) → %x = %y}
#eval ockham.eval fo!{∃ x. Tet(%x) ∧ Large(%x)}
#eval ockham.eval fo!{∃ x. ∃ y. Larger(%x, %y) ∧ ¬ Large(%x)}
#eval ockham.eval fo!{∀ x. ∀ y. Dodec(%x) ∧ Dodec(%y) → x = y}
#eval ockham.eval fo!{¬ ∀ y. Cube(%y) → Small(%y)}
#eval ockham.eval fo!{∀ x. Large(%x) ↔ Tet(%x)}
#eval ockham.eval fo!{∀ x. ∀ y. Larger(%x, %y) → BackOf(%x, %y)}
#eval ockham.eval fo!{∃ x. ∃ y. Cube(%x) ∧ Tet(%y) ∧ LeftOf(%x, %y) ∧ Smaller(%x, %y)}
#eval ockham.eval fo!{∃ x. ∃ y. Small(%x) ∧ Large(%y) ∧ ∀ z. Between(%z, %x, %y) ↔ Cube(%z)}
#eval ockham.eval fo!{∀ x. Small(%x) ↔ (∀ y. ¬ %y = %x → LeftOf(%x, %y))}

/-
5B.

Create as world (with as many objects as you like) in which all the following sentences are true.
-/

def arnault : World := [
  -- add objects here
]

-- Tip: You can pin this display open using the 📌 icon in the Lean Infoview
#eval arnault.show
-- #3d_world arnault

#eval arnault.eval fo!{∀ x. ∀ y. (SameRow(%x, %y) ∧ SameCol(%x, %y)) → %x = %y}
#eval arnault.eval fo!{∃ x. ∃ y. ∃ z. Cube(%x) ∧ Dodec(%y) ∧ Tet(%z)}
#eval arnault.eval fo!{¬ ∃ x. Large(%x)}
#eval arnault.eval fo!{∀ x. Dodec(%x) → ∃ y. Cube(%y) ∧ BackOf(%x, %y)}
#eval arnault.eval fo!{∀ x. Tet(%x) → ∃ y. ∃ z. Between(%x, %y, %z)}
#eval arnault.eval fo!{∀ x. ∀ y. ∀ z. Between(%x, %y, %z) → Larger(%x, %y)}
#eval arnault.eval fo!{∃ x. ∃ y. ¬ %x = %y ∧ ∀ w. %w = %x ∨ %w = %y → ∀ z. ¬ BackOf(%y, %x)}
#eval arnault.eval fo!{∀ x. ∀ y. Larger(%x, %y) → ∃ z. Between(%x, %y, %z)}
#eval arnault.eval fo!{∀ x. Cube(%x) ↔ ∃ y. Tet(%y) ∧ BackOf(%y, %x)}
#eval arnault.eval fo!{¬ ∀ x. ∀ y. LeftOf(%x, %y) ∨ RightOf(%x, %y)}
#eval arnault.eval fo!{∃ x. ∃ y. ¬ (FrontOf(%x, %y) ∨ BackOf(%x, %y))}

end
