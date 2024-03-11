import LAMR

inductive LBinTree (α : Type)
| empty : LBinTree α
| node  : α → LBinTree α → LBinTree α → LBinTree α

open LBinTree

def allLe : LBinTree Nat → Nat → Bool
| empty, _      => true
| node m s t, n => m ≤ n && allLe s n && allLe t n

def allGe : LBinTree Nat → Nat → Bool
| empty, _      => true
| node m s t, n => n ≤ m && allGe s n && allGe t n

def ordered : LBinTree Nat → Bool
| empty      => true
| node n s t => ordered s && ordered t && allLe s n && allGe t n

def insert (n : Nat) : LBinTree Nat → LBinTree Nat
| empty => node n empty empty
| node m s t => if n ≤ m then node m (insert n s) t else node m s (insert n t)
