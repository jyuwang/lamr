import LAMR

/-
exercise 5
-/

-- you can test whether two strings are equal
#eval if "p" = "q" then "yes" else "no"

namespace PropForm

-- Replace this with the real definition.
def substitute : PropForm → PropForm → String → PropForm
  | PropForm.tr, _, _ => PropForm.tr
  | PropForm.fls, _, _ => PropForm.fls
  | PropForm.var x, s, varName => if x = varName then s else PropForm.var x
  | PropForm.conj p1 p2, s, varName => PropForm.conj (substitute p1 s varName) (substitute p2 s varName)
  | PropForm.disj p1 p2, s, varName => PropForm.disj (substitute p1 s varName) (substitute p2 s varName)
  | PropForm.impl p1 p2, s, varName => PropForm.impl (substitute p1 s varName) (substitute p2 s varName)
  | PropForm.neg p, s, varName => PropForm.neg (substitute p s varName)
  | PropForm.biImpl p1 p2, s, varName => PropForm.biImpl (substitute p1 s varName) (substitute p2 s varName)

end PropForm

-- Putting the definition in the `PropForm` namespace means you can use the
-- "anonymous projection" notation below.

#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "q"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "p"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "t"


/-
exercise 6
-/

-- On the right-hand side, Lean determines that `.tr` is `PropForm.tr`
-- because it is expecting a `PropForm` there.

-- Replace this with the real definition.
-- def CnfForm.toPropForm (F : CnfForm) : PropForm :=
--   .tr

namespace CnfForm

def litToPropForm : Lit → PropForm
  | Lit.pos varName => PropForm.var varName
  | Lit.neg varName => PropForm.neg (PropForm.var varName)
  | Lit.tr => PropForm.tr
  | Lit.fls => PropForm.fls

def clauseToPropForm (c : Clause) : PropForm :=
  match c with
  | [] => PropForm.fls  -- An empty clause represents falsity in a CNF context.
  | l::ls => ls.foldl (fun acc lit => PropForm.disj acc (litToPropForm lit)) (litToPropForm l)

def toPropForm (F : CnfForm) : PropForm :=
  match F with
  | [] => PropForm.tr  -- An empty CNF is considered to be true.
  | c::cs => cs.foldl (fun acc clause => PropForm.conj acc (clauseToPropForm clause)) (clauseToPropForm c)

end CnfForm

#eval toString cnf!{p q r, r -s t, q t}
#eval toString cnf!{p q r, r -s t, q t}.toPropForm


/-
exercise 7
-/

-- Remember the notation for propositional assignments.
#eval propassign!{p, q, -r}.eval "r"

-- Here are some operations on Booleans.
#eval true && false
#eval true || false
#eval !true

-- You will have to define auxiliary functions, like evaluation
-- for literals and clauses.

-- Rather than open the namespace explicitly, you can put the
-- function in the `CnfForm` namespace like this.
-- In the recursive call, refer to the function as just `eval`.

-- Evaluates a literal under a given propositional assignment.
def CnfForm.evalLiteral (v : PropAssignment) : Lit → Bool
  | Lit.tr => true
  | Lit.fls => false
  | Lit.pos s => v.eval s
  | Lit.neg s => !(v.eval s)

-- Evaluates a clause (a disjunction of literals) under a given propositional assignment.
-- Note that a clause is true if at least one of its literals is true.
def CnfForm.evalClause (v : PropAssignment) (clause : Clause) : Bool :=
  clause.any (λ lit => evalLiteral v lit)

-- Evaluates a CNF formula (a conjunction of clauses) under a given propositional assignment.
-- Note that a CNF formula is true if all of its clauses are true.
-- Replace this with the real definition.
def CnfForm.eval : CnfForm → PropAssignment → Bool
  | cnf, v => cnf.all (λ clause => CnfForm.evalClause v clause)

#eval cnf!{p q r, r -s t, q t}.eval propassign!{-p, -q, -r, s, -t}

/-
exercise 8
-/

#check NnfForm
#check PropForm.toNnfForm

-- Replace this with the real definition.
inductive EnnfForm :=
  | lit  (l : Lit)       : EnnfForm
  | conj (p q : EnnfForm) : EnnfForm
  | disj (p q : EnnfForm) : EnnfForm
  | biImpl (p q : EnnfForm) : EnnfForm
  deriving Repr

namespace EnnfForm

-- Replace this with the real definition.
def toPropForm : EnnfForm → PropForm
  | EnnfForm.lit l => match l with
      | Lit.tr => PropForm.tr
      | Lit.fls => PropForm.fls
      | Lit.pos p => PropForm.var p
      | Lit.neg p => PropForm.neg (PropForm.var p)
  | EnnfForm.conj p q => PropForm.conj (toPropForm p) (toPropForm q)
  | EnnfForm.disj p q => PropForm.disj (toPropForm p) (toPropForm q)
  | EnnfForm.biImpl p q => PropForm.biImpl (toPropForm p) (toPropForm q)


end EnnfForm

-- Helper needed to negate EnnfForm
def EnnfForm.neg : EnnfForm → EnnfForm
  | EnnfForm.lit l => match l with
    | Lit.tr => EnnfForm.lit Lit.fls
    | Lit.fls => EnnfForm.lit Lit.tr
    | Lit.pos p => EnnfForm.lit (Lit.neg p)
    | Lit.neg p => EnnfForm.lit (Lit.pos p)
  | EnnfForm.conj p q => EnnfForm.disj (p.neg) (q.neg)
  | EnnfForm.disj p q => EnnfForm.conj (p.neg) (q.neg)
  | EnnfForm.biImpl p q => EnnfForm.biImpl (p.neg) q


namespace PropForm

-- Replace this with the real definition.
def toEnnfForm : PropForm → EnnfForm
  | tr     => EnnfForm.lit Lit.tr
  | fls    => EnnfForm.lit Lit.fls
  | var p  => EnnfForm.lit (Lit.pos p)
  | neg p  => (toEnnfForm p).neg
  | conj p q => EnnfForm.conj (toEnnfForm p) (toEnnfForm q)
  | disj p q => EnnfForm.disj (toEnnfForm p) (toEnnfForm q)
  | impl p q =>
      EnnfForm.disj (toEnnfForm p).neg (toEnnfForm q)
  | biImpl p q => EnnfForm.biImpl (toEnnfForm p) (toEnnfForm q)

end PropForm

#eval prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm
#eval toString <| prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm.toPropForm
