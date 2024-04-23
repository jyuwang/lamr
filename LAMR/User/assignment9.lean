import LAMR.Util.FirstOrder.Atp
open Std

-- The parts you need to fill in are labeled "TODO".

/-
These helper functions may be useful.
-/

namespace Std.AssocList

-- this function takes as input a and m, and returns the value associated with a in m.
def find! [BEq α] [Inhabited β] (a : α) (m : AssocList α β) : β :=
  match m.find? a with
    | some b => b
    | none   => default

end Std.AssocList


def getVal (s : String) (m : AssocList String Sexp) : Nat :=
  match evalNumConst (m.find! s) with
    | some n => n
    | none   => 0

/-
These examples may be helpful. See also the examples in the folder
Examples/using_smt_solvers.
-/

def smt_example_input :=
let xmin := "5"
let ymin := "7"
sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const z Int)
    (assert (<= {xmin} x))
    (assert (<= {ymin} y))
    (assert (<= (+ x y) z))
    (check-sat)
    (get-model)
  }

def smt_example : IO Unit := do
  -- turn on verbose output to see what is going on.
  let out ← callZ3 smt_example_input (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "Model as an Sexpr"
    IO.println m
    IO.println ""
    let assocList := decodeModelConsts m
    IO.println "Model as an association list:"
    IO.println assocList
    let x := getVal "x" assocList
    let y := getVal "y" assocList
    let z := getVal "z" assocList
    IO.println ""
    IO.println s!"x := {x}, y := {y}, z := {z}"
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval smt_example

-- There is also notation for splicing in another list of sexprs.

def smt_example_input2 : List Sexp := Id.run do
  let mut decls : Array Sexp := #[]
  for var in ["x", "y", "z"] do
    decls := decls.push sexp!{(declare-const {var} Int)}
  let xmin := "5"
  let ymin := "7"
  sexps!{
      (set-logic QF_LIA)
      (set-option :produce-models true)
      ...{decls.toList}
      (assert (<= {xmin} x))
      (assert (<= {ymin} y))
      (assert (<= (+ x y) z))
      (check-sat)
      (get-model)
    }

def smt_example2 : IO Unit := do
  let out ← callZ3 smt_example_input (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    let x := getVal "x" assocList
    let y := getVal "y" assocList
    let z := getVal "z" assocList
    IO.println s!"x := {x}, y := {y}, z := {z}"
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval smt_example2

/-
Problem 1.
-/

-- TODO: Add the relevant constraints
-- Goal is FOF / SCS = .LAMRLAMR...
-- HINT: .LAMRLAMR... = LAMR / 9999
-- Therefore FOF / SCS = LAMR / 9999
-- Therefore FOF * 9999 = SCS * LAMR
def problem1_input :=
sexps!{
    (set-logic QF_NIA)
    (set-option :produce-models true)
    (declare-const f Int)
    (declare-const o Int)
    (declare-const s Int)
    (declare-const c Int)
    (declare-const l Int)
    (declare-const a Int)
    (declare-const m Int)
    (declare-const r Int)
    -- constraint so that each is a digit
    (assert (and (>= f 0) (<= f 9)))
    (assert (and (>= o 0) (<= o 9)))
    (assert (and (>= s 0) (<= s 9)))
    (assert (and (>= c 0) (<= c 9)))
    (assert (and (>= l 0) (<= l 9)))
    (assert (and (>= a 0) (<= a 9)))
    (assert (and (>= m 0) (<= m 9)))
    (assert (and (>= r 0) (<= r 9)))
    -- constraint so that each is distinct
    (assert (distinct f o s c l a m r))
    -- declare constant so that FOF is F * 100 + O * 10 + F
    -- (assert (= FOF (+ (* f 100) (* o 10) f)))
    -- declare constant so that SCS is S * 100 + C * 10 + S
    -- (assert (= SCS (+ (* s 100) (* c 10) s)))
    -- declare constant so that LAMR is L * 1000 + A * 100 + M * 10 + R
    -- (assert (= LAMR (+ (* l 1000) (* a 100) (* m 10) r)))
    -- constraint so that FOF * 9999 = SCS * LAMR
    (assert (= (* (+ (* f 100) (* o 10) f) 9999) (* (+ (* s 100) (* c 10) s) (+ (* l 1000) (* a 100) (* m 10) r))))
    (check-sat)
    (get-model)
  }

-- TODO: call the solver and print out the answer

def problem1 : IO Unit := do
  let out ← callZ3 problem1_input (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    IO.println assocList
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval problem1

/-
Problem 2.
-/

-- Here are some helper functions

def distinctSexp (consts : List String) : Sexp :=
  Sexp.expr <| [Sexp.atom "distinct"] ++ consts.map Sexp.atom

def multiAritySexp (op : String) (args : List Sexp): Sexp :=
  Sexp.expr <| (Sexp.atom op) :: args

def natConst (i : Nat) := s!"{i}"
def node (i : Nat) := s!"v{i}"
def edge (i : Nat) := s!"e{i}"

#eval distinctSexp [node 0, node 1, node 2]
#eval multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]
#eval sexp!{(assert {multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]})}

-- TODO: The constraints from part A.

def gracefulLabelingA (n : Nat) : Array Sexp := Id.run do
  let mut body : Array Sexp := #[]

  -- declare consts for each node
  let mut nodes: Array Sexp := #[]
  for i in [0:n+1] do
    nodes := nodes.push sexp!{(declare-const {node i} Int)}
  -- declare consts for each edge
  let mut edges: Array Sexp := #[]
  for i in [1:n+1] do
    edges := edges.push sexp!{(declare-const {edge i} Int)}
  -- create list of strings for each node and edge for the distinct constraint
  let mut strNodes : List String := []
  for i in [0:n+1] do
    strNodes := node i :: strNodes
  let mut strEdges : List String := []
  for i in [1:n+1] do
    strEdges := edge i :: strEdges

  let mut asserts: Array Sexp := #[]
  -- create the distinct constraints
  asserts := asserts.push sexp!{(assert {distinctSexp strNodes})}
  asserts := asserts.push sexp!{(assert {distinctSexp strEdges})}

  -- each node is between 0 and n
  for i in [0:n+1] do
    asserts := asserts.push sexp!{(assert (and (>= {node i} 0) (<= {node i} {natConst n})))}

  -- each edge is between 1 and n
  for i in [1:n+1] do
    asserts := asserts.push sexp!{(assert (and (>= {edge i} 1) (<= {edge i} {natConst n})))}

  -- each edge is labeled with the difference of the corresponding vertex labels
  for i in [1:n+1] do
    asserts := asserts.push sexp!{(assert (or (= {edge i} (- {node i} {node (i - 1)})) (= {edge i} (- {node (i - 1)} {node i}))))}

  body := body ++ nodes ++ edges ++ asserts

  body

-- Do a reality check.

#eval gracefulLabelingA 9 |>.toList

-- TODO: the constraints from part B.
-- add constraints that enforce that at for each vertex label 0 to |E|,
-- there exists a vertex with that label.
-- Similarly, enforce that each edge label 1 to |E|, there exists an edge with that label
def gracefulLabelingB (n : Nat) : Array Sexp := Id.run do
  let mut body : Array Sexp := gracefulLabelingA n

  let mut asserts : Array Sexp := #[]
  -- for each vertex label 0 to |E|, there exists a vertex with that label
  for i in [0:n+1] do
    let ors := (List.range (n+1)).map (fun j => sexp!{(= {node j} {natConst i})})
    asserts := asserts.push sexp!{(assert (or {multiAritySexp "or" ors}))}

  -- for each edge label 1 to |E|, there exists an edge with that label
  for i in [1:n+1] do
    let ors := (List.range (n)).map (fun j => sexp!{(= {edge (j+1)} {natConst i})})
    asserts := asserts.push sexp!{(assert (or {multiAritySexp "or" ors}))}

  body := body ++ asserts

  body

-- Another reality check.

#eval gracefulLabelingB 9 |>.toList

def gracefulLabelingProblem (n : Nat) : List Sexp :=
sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    ...{ gracefulLabelingB n |>.toList }
    (check-sat)
    (get-model)
  }

-- TODO: call the solver and print out the solution.
def gracefulLabeling (n : Nat) : IO Unit := do
  let out ← callZ3 (gracefulLabelingProblem n) (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    let edges := List.range n
    let nodes := List.range (n+1)
    let edgeID := edges.map (fun i => getVal (edge (i+1)) assocList)
    let nodeID := nodes.map (fun i => getVal (node i) assocList)
    for i in [0:n] do
      IO.print s!"({nodeID[i]!})"
      if i < n then
        IO.print s!"-{edgeID[i]!}-" -- print the edge label
    IO.println s!"({nodeID[n]!})"
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval gracefulLabeling 9

/-
Problem 3.
-/

-- More helper functions.

def xmin (i : Nat) := s!"xmin_{i}"
def xmax (i : Nat) := s!"xmax_{i}"
def ymin (i : Nat) := s!"ymin_{i}"
def ymax (i : Nat) := s!"ymax_{i}"

-- TODO: Define the list of constant declarations and assertions that say that
-- the almost squares of orders 1 to n cover the almost square of order m.
def partA (n m : Nat) : Array Sexp := Id.run do
  -- in range 1 to n+1, declare consts for xmin and xmax and ymin and ymax
  let mut consts : Array Sexp := #[]
  for i in [1:n+1] do
    consts := consts.push (sexp!{(declare-const {xmin i} Int)})
    consts := consts.push (sexp!{(declare-const {xmax i} Int)})
    consts := consts.push (sexp!{(declare-const {ymin i} Int)})
    consts := consts.push (sexp!{(declare-const {ymax i} Int)})
  -- Express constraints that ensure that the almost square of order n covers exactly a subgrid of n × (n + 1) or (n + 1) × n
  let mut asserts : Array Sexp := #[]
  for i in [1:n+1] do
    -- xmin i <= xmax i
    -- ymin i <= ymax i
    asserts := asserts.push (sexp!{(assert (and (<= {xmin i} {xmax i}) (<= {ymin i} {ymax i})))})

    -- both min's at least 1
    asserts := asserts.push (sexp!{(assert (and (<= 1 {xmin i}) (<= 1 {ymin i})))})
    -- xmax is at most m+1 and ymax is at most m
    asserts := asserts.push (sexp!{(assert (and (<= {xmax i} {natConst (m+1)}) (<= {ymax i} {natConst m})))})

    -- enforce the relation between all four variables
    asserts := asserts.push (sexp!{(assert (or (and (= {natConst (i - 1)} (- {xmax i} {xmin i})) (= {natConst (i)} (- {ymax i} {ymin i}))) (and (= {natConst (i)} (- {xmax i} {xmin i})) (= {natConst (i-1)} (- {ymax i} {ymin i})))) )})

  -- join the consts and asserts
  consts ++ asserts

-- For each pair of almost squares, express the constraint that they cannot overlap each other, i.e.,
-- there is no cell that is covered by multiple almost squares.
def partB (n m : Nat) : Array Sexp := Id.run do
  let mut asserts : Array Sexp := #[]
  -- for i in [1:n+1] do
  for i in [1:n+1] do
    for j in [1:n+1] do
      if i != j then
        asserts := asserts.push (sexp!{(assert (or (< {xmax i} {xmin j}) (< {xmax j} {xmin i}) (< {ymax i} {ymin j}) (< {ymax j} {ymin i})))})
      -- else
  asserts

def AlmostToSmt (n m : Nat) : List Sexp :=
  let helperResultsA := partA n m
  let helperResultsB := partB n m
  let helperResults := helperResultsA ++ helperResultsB
  sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    ...{helperResults.toList}
    (check-sat)
    (get-model)
  }


#eval AlmostToSmt 8 15

def String.ljust n s :=
  s ++ "".pushn ' ' (n - s.length)

-- TODO: Write a procedure to print it out

-- this function takes in the model and prints out the almost square
-- for example, if the model is:
-- [(ymin_3, 1), (xmax_2, 5), (ymax_3, 4), (ymax_1, 1), (ymin_2, 2), (ymax_2, 4), (xmax_3, 3), (ymin_1, 1), (xmin_3, 1), (xmin_1, 4), (xmin_2, 4), (xmax_1, 5)]
-- then the almost square would be:
-- 3 3 3 2 2
-- 3 3 3 2 2
-- 3 3 3 2 2
-- 3 3 3 1 1
def printAlmostSquare (n m : Nat) (model : Sexp) : IO Unit := do
  let assocList := decodeModelConsts model
  -- initialize empty almost square
  let mut almostSquare : Array (Array String) :=
    Array.mkArray m (Array.mkArray (m + 1) "_")

  -- for each almost square, fill in the almost square
  for i in [1:n+1] do
    let xMin := getVal (xmin i) assocList
    let xMax := getVal (xmax i) assocList
    let yMin := getVal (ymin i) assocList
    let yMax := getVal (ymax i) assocList

    -- fill in the almost square
    for x in [xMin:xMax + 1] do
      for y in [yMin:yMax + 1] do
        let temp := ((almostSquare.get! (m - y)).set! (x - 1) (toString i)) -- temp is the row of the almost square
        almostSquare := almostSquare.set! (m - y) temp -- set the row of the almost square

  -- print the final almost square
  for row in almostSquare do
    for square in row do
      IO.print square
      IO.print " "
    IO.println ""


-- Call the SAT solver to construct the almost square.
-- This ran in under 1 second
#eval (do
  let cmds := AlmostToSmt 8 15
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println <| decodeModelConsts m
    IO.println "SAT with assignment:"
    for (x, b) in decodeModelConsts m do
      IO.println s!"{x} ↦ {evalNumConst b |>.get!}"
    IO.println "\nResult:"
    printAlmostSquare 8 15 m
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

  : IO Unit)

-- TODO: Define the bitvector-based encoding.
def partABv (n m : Nat) : Array Sexp := Id.run do
  -- in range 1 to n+1, declare consts for xmin and xmax and ymin and ymax
  let mut consts : Array Sexp := #[]
  for i in [1:n+1] do
    consts := consts.push (sexp!{(declare-const {xmin i} (_ BitVec 16))})
    consts := consts.push (sexp!{(declare-const {xmax i} (_ BitVec 16))})
    consts := consts.push (sexp!{(declare-const {ymin i} (_ BitVec 16))})
    consts := consts.push (sexp!{(declare-const {ymax i} (_ BitVec 16))})
  -- Express constraints that ensure that the almost square of order n covers exactly a subgrid of n × (n + 1) or (n + 1) × n
  let mut asserts : Array Sexp := #[]
  for i in [1:n+1] do
    -- xmin i <= xmax i
    -- ymin i <= ymax i
    asserts := asserts.push (sexp!{(assert (and (bvsle {xmin i} {xmax i}) (bvsle {ymin i} {ymax i})))})

    -- both min's at least 1
    asserts := asserts.push (sexp!{(assert (and (bvsle {toBVConst 16 1} {xmin i}) (bvsle {toBVConst 16 1} {ymin i})))})
    -- xmax is at most m+1 and ymax is at most m
    asserts := asserts.push (sexp!{(assert (and (bvsle {xmax i} (bvadd {toBVConst 16 m} {toBVConst 16 1})) (bvsle {ymax i} {toBVConst 16 m})))})

    -- -- enforce the relation between all four variables
    asserts := asserts.push (sexp!{(assert (or (and (= (bvsub {toBVConst 16 i} {toBVConst 16 1}) (bvsub {xmax i} {xmin i})) (= {toBVConst 16 i} (bvsub {ymax i} {ymin i}))) (and (= {toBVConst 16 i} (bvsub {xmax i} {xmin i})) (= (bvsub {toBVConst 16 i} {toBVConst 16 1}) (bvsub {ymax i} {ymin i}))))) })
  -- join the consts and asserts
  consts ++ asserts

def partBBv (n m : Nat) : Array Sexp := Id.run do
  let mut asserts : Array Sexp := #[]
  -- for i in [1:n+1] do
  for i in [1:n+1] do
    for j in [1:n+1] do
      if i != j then
        asserts := asserts.push (sexp!{(assert (or (bvult {xmax i} {xmin j}) (bvult {xmax j} {xmin i}) (bvult {ymax i} {ymin j}) (bvult {ymax j} {ymin i})))})
      -- else
  asserts

def almostToSmtBv (n m : Nat) : List Sexp :=
  let helperResultsA := partABv n m
  let helperResultsB := partBBv n m
  let helperResults := helperResultsA ++ helperResultsB
  sexps!{
    (set-logic QF_BV)
    (set-option :produce-models true)
    ...{helperResults.toList}
    (check-sat)
    (get-model)
  }

#eval almostToSmtBv 8 15

-- Call the SAT solver to construct the result square.
-- This ran in under 1 second as well
#eval (do
  let cmds := almostToSmtBv 8 15
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "SAT with assignment:"
    for (x, b) in decodeModelConsts m do
      IO.println s!"{x} ↦ {evalNumConst b |>.get!}"
    IO.println "\nResult:"
    printAlmostSquare 8 15 m
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

  : IO Unit)

#eval (do
  let cmds := almostToSmtBv 20 55
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "SAT with assignment:"
    for (x, b) in decodeModelConsts m do
      IO.println s!"{x} ↦ {evalNumConst b |>.get!}"
    IO.println "\nResult:"
    printAlmostSquare 20 55 m
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

  : IO Unit)

-- Result:
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 7 7 7 7 7 7 7 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 6 6 6 6 6 6 6 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 6 6 6 6 6 6 6 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 6 6 6 6 6 6 6 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 6 6 6 6 6 6 6 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 6 6 6 6 6 6 6 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 6 6 6 6 6 6 6 14 14 14 14 14 14 14 14 14 14 14 14 14 14 14 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 2 2 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 2 2 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 2 2 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 17 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16 16
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 4 4 4 4 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 4 4 4 4 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 4 4 4 4 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 4 4 4 4 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 10 10 10 10 10 10 10 10 10 10 10 8 8 8 8 8 8 8 8 8 4 4 4 4 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 10 10 10 10 10 10 10 10 10 10 10 1 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 10 10 10 10 10 10 10 10 10 10 10 1 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 13 13 13 13 13 13 13 13 13 13 13 13 13
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 3 3 3 9 9 9 9 9 9 9 9 9 9
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 3 3 3 9 9 9 9 9 9 9 9 9 9
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 3 3 3 9 9 9 9 9 9 9 9 9 9
-- 11 11 11 11 11 11 11 11 11 11 11 11 12 12 12 12 12 12 12 12 12 12 12 12 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 18 3 3 3 9 9 9 9 9 9 9 9 9 9
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 5 5 5 5 5 5 9 9 9 9 9 9 9 9 9 9
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 5 5 5 5 5 5 9 9 9 9 9 9 9 9 9 9
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 5 5 5 5 5 5 9 9 9 9 9 9 9 9 9 9
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 5 5 5 5 5 5 9 9 9 9 9 9 9 9 9 9
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 5 5 5 5 5 5 9 9 9 9 9 9 9 9 9 9
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
-- 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 20 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 19 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15 15
