import LAMR

/-
Exercise 5.
-/

namespace CnfForm

-- Function to negate a literal, flipping its truth value
def negateLit : Lit → Lit
| Lit.tr => Lit.fls
| Lit.fls => Lit.tr
| Lit.pos s => Lit.neg s
| Lit.neg s => Lit.pos s

-- Function to flip the truth values of all literals in a clause
def flipClause : Clause → Clause
| clause => clause.map negateLit

-- Function to flip the truth values of all literals in a CNF formula
def flipCnf : CnfForm → CnfForm
| cnf => cnf.map flipClause

end CnfForm

def combinations : List Lit → Nat → List (List Lit)
| _, 0 => [[]]  -- Base case: only one combination of length 0, the empty combination
| [], _ => []   -- If no elements are left, no combinations can be formed
| (x :: xs), k =>
  let withX := combinations xs (k - 1) |>.map (λ combo => x :: combo)  -- Combinations that include x
  let withoutX := combinations xs k                                    -- Combinations that do not include x
  withX ++ withoutX


def atLeastKTrue (lst : List Lit) (k : Nat) : CnfForm :=
  let n := lst.length
  let combs := combinations lst (n-k+1)
  combs.map (fun comb => Clause.mk comb) -- Convert each combination into a clause

-- Helper function to generate the clauses for "at most k literals are true"

def atMostKTrue (lst : List Lit) (k : Nat) : CnfForm :=
  let combs := combinations lst (k + 1)
  let clauses := combs.map (fun comb => comb.map (fun lit => lit.negate))
  CnfForm.mk clauses
  -- combs.map (fun comb => Clause.mk comb)

-- Main function to generate the CNF form
def exactlyKTrue (lst : List Lit) (k : Nat) : CnfForm :=
  let atLeast := atLeastKTrue lst k
  let atMost := atMostKTrue lst k
  atLeast.conj atMost -- Combine the two sets of clauses


def exampleLiterals := [lit!{a}, lit!{b}, lit!{c}]
def k := 1
#eval atLeastKTrue exampleLiterals k
#eval atMostKTrue exampleLiterals k
#eval exactlyKTrue exampleLiterals k
