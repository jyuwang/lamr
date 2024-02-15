import LAMR

/-
Exercise 1.
-/

-- this may be helpful
def Lit.var : Lit → String
  | tr => ""
  | fls => ""
  | pos s => s
  | neg s => s

-- these may be helpful also
#check List.all
#check List.any
#check List.filter

/-
Remember a `Clause` is a list of literals, so you can do this, for example.
-/
#eval let clause : Clause := [lit!{p}, lit!{-q}, lit!{r}]
      clause.any (fun l => l.var == "p")

namespace PropAssignment

open Lit

-- check if a clause is touched by the assignment
def clauseIsTouched (τ : PropAssignment) (c : Clause) : Bool :=
  c.any (fun l => τ.mem l.var)

-- convert an option to a bool
def optionToBool (o : Option Bool) : Bool :=
  match o with
  | some b => b
  | none => false

-- check if a touched clause is satisfied by the assignment
def touchedClauseIsSatisfied (τ : PropAssignment) (c : Clause) : Bool :=
  c.any (fun l => optionToBool (τ.evalLit? l))  -- Check if any literal in the clause is satisfied by τ

-- -- ** Fill in this definition. **
def isAutarky (τ : PropAssignment) (φ : CnfForm) : Bool :=
  φ.all (fun c =>
    if clauseIsTouched τ c
    then touchedClauseIsSatisfied τ c
    else true)  -- ff a clause is not touched, it's considered satisfied for the purpose of being an autarky

-- for testing
#eval isAutarky [] cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{p} cnf!{p q r, -p -q -r} == false
#eval isAutarky propassign!{p} cnf!{p q r, -q -r} == true
#eval isAutarky propassign!{p, -q} cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{-q} cnf!{-p -q -r} == true
#eval isAutarky propassign!{-q} [] == true
#eval isAutarky (propassign!{p, q, -u, -r}) (cnf!{p q u -v, -u, -r, ⊥, ⊤}) == true
#eval isAutarky (propassign!{p, -q, v}) (cnf!{p q u -v, -u, u, -v}) == false
#eval isAutarky (propassign!{p, -q, v, w, a, b, c, d}) (cnf!{p q u -v, -u, u}) == true


-- Write in Lean a function getPure that takes a CNF formula Γ : CnfForm and
-- returns a List Lit of all pure literals in Γ. The function does not need to find all pure literals
-- until fixpoint, only the literals the are pure in Γ.
-- ** Fill in this definition. **
def getPure (φ : CnfForm) : List Lit :=
  -- flatten the list of clauses into a list of literals
  let lits := φ.join

  -- function to check if the negation of a literal exists in the list of literals
  let negationExists (l : Lit) (lits : List Lit) : Bool :=
    lits.any (fun l' => l'.var == l.var && l != l')

  -- filter the list of literals to only include those that are pure
  lits.filter (fun l => ¬ negationExists l lits)


-- for testing
def eqSets [BEq α] (k l : List α) : Bool :=
  k.all l.contains &&
  l.all k.contains
infix:40 " eqSets " => eqSets

#eval getPure cnf!{} eqSets []
#eval getPure cnf!{p} eqSets [lit!{p}]
#eval getPure cnf!{-p} eqSets [lit!{-p}]
#eval getPure cnf!{-p, p} eqSets []
#eval getPure cnf!{p, q} eqSets [lit!{p}, lit!{q}]
#eval getPure cnf!{p, q, -p} eqSets [lit!{q}]
#eval getPure cnf!{p, -q, -p} eqSets [lit!{-q}]
#eval getPure cnf!{q p, -q p, p} eqSets [lit!{p}]

end PropAssignment

/-
Exercise 2.
-/

-- Part A) Write this function
def rectangleConstraints (m n k : Nat) : CnfForm :=
  []

/-
These should be satisfiable.
-/

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => IO.println τ.toString

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => IO.println τ.toString

/-
Decode the solutions.
-/

-- This may be helpful; it tests whether a literal is positive.
def Lit.isPos : Lit → Bool
  | pos s => true
  | _     => false

-- ** Write this part: interpret the positive literals as a rectangle. **
def decodeSolution (m n k: Nat) (τ : List Lit) : Except String (Array (Array Nat)) := do
  let mut s : Array (Array Nat) := mkArray m (mkArray n 0)
  -- use the literals to fill in the rectangle
  return s

def outputSolution (m n k : Nat) (τ : List Lit) : IO Unit :=
  let posLits := τ.filter Lit.isPos
  match decodeSolution m n k posLits with
    | Except.error s => IO.println s!"Error: {s}"
    | Except.ok rect =>
        for i in [:m] do
          for j in [:n] do
            IO.print s!"{rect[i]![j]!} "
          IO.println ""

-- Try it out.

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 10 10 3 τ

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 9 12 3 τ


/-
Exercise 3.
-/

namespace Resolution

/--
The resolution Step.
-/
def resolve (c₁ c₂ : Clause) (var : String) : Clause :=
  (c₁.erase (Lit.pos var)).union' (c₂.erase (Lit.neg var))

/--
A line of a resolution proof is either a hypothesis or the result of a
resolution step.
-/
inductive Step where
  | hyp (clause : Clause) : Step
  | res (var : String) (pos neg : Nat) : Step
deriving Inhabited

def Proof := Array Step deriving Inhabited

-- Ignore this: it is boilerplate to make `GetElem` work.
instance : GetElem Proof Nat Step (fun xs i => i < xs.size) :=
  inferInstanceAs (GetElem (Array Step) _ _ _)

-- determines whether a proof is well-formed
def Proof.wellFormed (p : Proof) : Bool := Id.run do
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp _ => continue
      | Step.res _ pos neg =>
          if i ≤ pos ∨ i ≤ neg then
            return false
  true

-- prints out the proof
def Proof.show (p : Proof) : IO Unit := do
  if ¬ p.wellFormed then
    IO.println "Proof is not well-formed."
    return
  let mut clauses : Array Clause := #[]
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp c =>
          clauses := clauses.push c
          IO.println s!"{i}: hypothesis: {c}"
      | Step.res var pos neg =>
          let resolvent := resolve clauses[pos]! clauses[neg]! var
          clauses := clauses.push resolvent
          IO.println s!"{i}: resolve {pos}, {neg} on {var}: {resolvent}"

end Resolution

section
open Resolution

def example1 : Proof := #[
  .hyp clause!{p q},
  .hyp clause!{-p},
  .hyp clause!{-q},
  .res "p" 0 1,
  .res "q" 3 2
]

#eval example1.wellFormed
#eval example1.show

def example2 : Proof := #[
  .hyp clause!{p q r},
  .hyp clause!{-p s},
  .hyp clause!{-q s},
  .hyp clause!{-r s},
  .hyp clause!{-s},
  .res "p" 0 1,
  .res "q" 5 2,
  .res "r" 6 3,
  .res "s" 7 4
]

#eval example2.wellFormed
#eval example2.show

-- ** Finish this to get a proof of ⊥.
def example3 : Proof := #[
  .hyp clause!{p q -r},
  .hyp clause!{-p -q r},
  .hyp clause!{q r -s},
  .hyp clause!{-q -r s},
  .hyp clause!{p r s},
  .hyp clause!{-p -r -s},
  .hyp clause!{-p q s},
  .hyp clause!{p -q -s},
  .res "r" 4 3,
  .res "s" 4 2,
  .res "s" 8 7,
  .res "r" 9 0,
  .res "q" 11 10, -- p
  .res "r" 2 5,
  .res "s" 3 5,
  .res "s" 6 13,
  .res "r" 1 14,
  .res "q" 15 16, -- ¬ p
  .res "p" 12 17 -- ⊥
]

#eval example3.wellFormed
#eval example3.show

end
