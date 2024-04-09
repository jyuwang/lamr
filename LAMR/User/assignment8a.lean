import LAMR.Util.FirstOrder
open Std
open FOTerm

-- Implement this.
-- Remember that you can use `xs.union ys` to compute the union of two lists without
-- introducing duplicates.
def collectRhsVars : List (FOTerm × FOTerm) → List String
    | [] => []
    | (_, app _ l) :: eqs => l.foldl (fun acc t => acc.union (t.freeVars)) (collectRhsVars eqs)
    | (_, var x) :: eqs =>
      if (collectRhsVars eqs).contains x
      then collectRhsVars eqs
      else x :: collectRhsVars eqs

-- Implement this.
-- You can use `x ∈ forbidden` to check if a string `x` is in the list `forbidden`.
-- You can use `s == t` for the Boolean equality test between terms.
-- partial def match_aux? (forbidden : List String) (env : AssocList String FOTerm) :
--       List (FOTerm × FOTerm) → Option (AssocList String FOTerm)
--   | [] => none
--   | (app f1 l1, app f2 l2) :: eqs => if f1 == f2 then match_aux? forbidden env (l1.zip l2 ++ eqs) else none
--   | (var x, t) :: eqs => if x ∈ forbidden then none else match_aux? forbidden env ((var x, t) :: eqs)
--   | (t, var x) :: _ => match_aux? forbidden env [(var x, t)]

partial def match_aux? (forbidden : List String) (env : AssocList String FOTerm) :
      List (FOTerm × FOTerm) → Option (AssocList String FOTerm)
  | [] => some env
  | (app f1 l1, app f2 l2) :: eqs =>
      if f1 == f2 ∧ l1.length = l2.length
      then match_aux? forbidden env (l1.zip l2 ++ eqs)
      else none
  | (var x, t) :: eqs =>
      if x ∈ forbidden
      then match t with
        | var y => if x == y then match_aux? forbidden env eqs else none
        | _ => none
      else if env.contains x
      then match env.find? x, t with
        | some (var y), var z => if y == z then match_aux? forbidden env eqs else none
        | some t', _ => if t == t' then match_aux? forbidden env eqs else none
        | _, _ => none
      else match_aux? forbidden (env.cons x t) eqs
  | (t, var x) :: eqs =>
      match t with
      | var y => if x ∈ forbidden ∧ x ≠ y then none else match_aux? forbidden env ((var x, t) :: eqs)
      | _ => match_aux? forbidden env ((var x, t) :: eqs)

def match? (eqs : List (FOTerm × FOTerm)) :=
  match_aux? (collectRhsVars eqs) AssocList.nil eqs

partial def matchAndApply (eqs : List (FOTerm × FOTerm)) : Option (List (FOTerm × FOTerm)) :=
  match match? eqs with
    | some l => let σ : FOAssignment FOTerm := l
                eqs.map (fun (s, t) => (subst σ s, subst σ t))
    | none   => none

-- no match
def ex1 := [ (term!{ f(%x, g(%y))}, term!{ f(f(%z), %w) }) ]

#eval toString <| match? ex1
#eval toString <| matchAndApply ex1

-- has a match
def ex2 := [ (term!{ f(%x, %y)}, term!{ f(f(%z), g(%w)) }) ]

#eval toString <| match? ex2
#eval toString <| matchAndApply ex2

-- no match
def ex3 := [ (term!{ f(%x, %y) }, term!{ f(%y, %x) }) ]

#eval toString <| match? ex3
#eval toString <| matchAndApply ex3

-- has a match
def ex4 := [ (term!{ f(g(%x0), %x1) }, term!{ f(g(%x2), a) }) ]

#eval toString <| match? ex4
#eval toString <| matchAndApply ex4

-- has a match
def ex5 := [ (term!{ f(%x0) }, term!{ f(%x2) }),
             (term!{ f(%x1) }, term!{ f(%x2) }),
             (term!{ f(%x2) }, term!{ f(%x2) }),
             (term!{ f(%x3) }, term!{ f(%x2) })]

#eval toString <| match? ex5
#eval toString <| matchAndApply ex5
