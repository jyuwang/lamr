-- PROBLEM 1:
-- Using operations on List, write a Lean function that for every n returns the list of all the divisors
-- of n that are less than n.

def divisors (n : Nat) : List Nat :=
  List.filter (λ d => n % d == 0) (List.range n)

#check divisors 10
#eval divisors 10

-- PROBLEM 2:
-- A natural number n is perfect if it is equal to the sum of the divisors less than n. Write a Lean
-- function (with return type Bool) that determines whether a number n is perfect. Use it to find
-- all the perfect numbers less than 1,000.

-- Sum of a list of natural numbers
def listSum (l : List Nat) : Nat :=
  List.foldl (λ acc x => acc + x) 0 l
#eval listSum [1,2,3,4,5]

-- Sum of the divisors of a natural number
def sumDivisors (n : Nat) : Nat :=
  listSum (divisors n)

def isPerfect (n : Nat) : Bool :=
  n == sumDivisors n ∧ n ≠ 0

-- def isPerfect (n : Nat) : Bool :=
--   n == listSum (divisors n)

#eval isPerfect 6

def perfectNumLessThan1000 : List Nat :=
  List.filter isPerfect (List.range 1000)


-- PROBLEM 3:
-- Define a recursive function sublists(ℓ) in Lean that, for every list ℓ, returns a list of all the
-- sublists of ℓ. For example, given the list [1, 2, 3], it should compute the list
-- [[], [1], [2], [3], [1, 2], [1, 3], [2, 3], [1, 2, 3]].
-- The elements need not be listed in that same order.

def sublists (l : List α) : List (List α) :=
  match l with
  | [] => [[]]
  | h::t => (sublists t).map (λ x => h::x) ++ sublists t

#eval sublists [1,2,3]


-- PROBLEM 4:
-- Consider a variation of the Towers of Hanoi puzzle where we assume the pegs A, B, and C are
-- in a row, and we are only allowed to transfer a disk to an adjacent peg, which is to say, moves
-- from A to C or vice-versa are ruled out.
-- Write a Lean program to output the list of moves required to move n disks.
def HanoiAdj: Nat → String → String → String → IO Unit
  | 0, _, _, _ => return ()
  | (n + 1), start, aux, finish => do
    HanoiAdj n start finish aux
    IO.println s!"Move disk {n + 1} from {start} to {aux} "
    HanoiAdj n finish aux start
    IO.println s!"Move disk {n + 1} from {aux} to {finish} "
    HanoiAdj n start aux finish

-- PROBLEM 5:
-- 1. Define a datatype LBinTree α in Lean. It should be similar to BinTree, as defined in the
-- textbook, but the node constructor should include the label, like the cons constructor for
-- List.

inductive LBinTree (α : Type)
  | empty : LBinTree α
  | node (label : α) (left : LBinTree α) (right : LBinTree α) : LBinTree α
  deriving Repr, DecidableEq, Inhabited

open LBinTree


-- 2. Define myTree : LBinTree Nat corresponding to the example above.
def myTree : LBinTree Nat :=
        LBinTree.node 5 (LBinTree.node 7 LBinTree.empty (LBinTree.node 3 LBinTree.empty LBinTree.empty))
        (LBinTree.node 6 (LBinTree.node 4 LBinTree.empty LBinTree.empty) (LBinTree.node 2 LBinTree.empty LBinTree.empty))

-- 3. Define a function addNodes : LBinTree Nat → Nat that adds up the nodes of a tree with
-- labels from Nat. On the example above, it should return 27.

def addNodes (Tree : LBinTree Nat) : Nat :=
  match Tree with
  | LBinTree.empty => 0
  | LBinTree.node label left right => label + addNodes left + addNodes right

#eval addNodes myTree

-- 4. Define a function toListInorder that creates a list with an inorder traversal (left subtree
-- first, then the node, then the right subtree). On the example above, it should return
-- [7, 3, 5, 4, 6, 2].

def toListInorder (Tree : LBinTree Nat) : List Nat :=
  match Tree with
  | LBinTree.empty => []
  | LBinTree.node label left right => toListInorder left ++ [label] ++ toListInorder right

#eval toListInorder myTree


-- PROBLEM 6:
-- Write a Lean procedure pascal which, on input n, outputs the first n rows of Pascal’s triangle.
-- We adopt the convention that the row numbers start with 0, so the row numbered n should
-- have n + 1 entries, n choose 0, n choose 1, . . . , n choose n. For example, on input 6, the
-- program should output the following:
-- 0: 1
-- 1: 1 1
-- 2: 1 2 1
-- 3: 1 3 3 1
-- 4: 1 4 6 4 1
-- 5: 1 5 10 10 5 1

partial def pascal (n : Nat) : IO Unit :=
  let rec helper (n : Nat) (k : Nat) : Nat :=
    if k == 0 || k == n then 1
    else helper (n - 1) (k - 1) + helper (n - 1) k

  for i in [0:n] do
    IO.print s!"{i}: "
    for j in [0:i+1] do
      IO.print s!"{helper i j} "
    IO.println ""

#eval pascal 6
