import LAMR.Util.FirstOrder.Atp
open Std

/-
This example illustrates the use of Vampire. The problem it solves
is as follows:

"A very special island is inhabited only by knights and knaves.
Knights always tell the truth, and knaves always lie. You meet two
inhabitants: Zoey and Mel. Zoey tells you that Mel is a knave. Mel
says, 'Neither Zoey nor I are knaves.' Who is a knight and who is
a knave?"

Notice that we model "X says Y" as "Knight(X) ↔ Y." Think about why this
make sense! Notice also that we model "Knave(X)" as "¬ Knight(X)".
-/

def knights_knaves_hypotheses : List FOForm := [
  fo!{Knight(Zoey) ↔ ¬ Knight(Mel)},
  fo!{Knight(Mel) ↔ Knight(Zoey) ∧ Knight(Mel) }
]

def knights_knaves_conclusion: FOForm :=
  fo!{Knight(Zoey) ∧ ¬ Knight(Mel) }

-- Make sure hypotheses are consistent.
#eval (do
  discard <| callVampireTptp knights_knaves_hypotheses fo!{⊥} (verbose := true)
  : IO Unit)

-- Show that the conclusion follows from the hypotheses.
#eval (do
  discard <| callVampireTptp knights_knaves_hypotheses knights_knaves_conclusion (verbose := true)
  : IO Unit)

/-
Use Vampire to verify the following inference, by filling in the hypotheses and conclusion.

Every honest and industrious person is healthy.
No grocer is healthy.
Every industrious grocer is honest.
Every cyclist is industrious.
Every unhealthy cyclist is dishonest.

Conclusion: No grocer is a cyclist.

(Represent "unhealthy" as the negation of "healthy", and "dishonest" and the negation of
"honest." Let the variables range over people.)
-/

def grocer_is_not_a_cyclist_hypotheses : List FOForm := [
  -- Every honest and industrious person is healthy.
  fo!{∀ x. Honest(%x) ∧ Industrious(%x) → Healthy(%x)},
  -- No grocer is healthy.
  fo!{∀ x. Grocer(%x) → ¬ Healthy(%x)},
  -- Every industrious grocer is honest.
  fo!{∀ x. Grocer(%x) ∧ Industrious(%x) → Honest(%x)},
  -- Every cyclist is industrious.
  fo!{∀ x. Cyclist(%x) → Industrious(%x)},
  -- Every unhealthy cyclist is dishonest.
  fo!{∀ x. Cyclist(%x) ∧ ¬ Healthy(%x) → Dishonest(%x)}
]

def grocer_is_not_a_cyclist_conclusion: FOForm :=
-- No grocer is a cyclist.
fo!{∀ x. Grocer(%x) → ¬ Cyclist(%x)}

-- Should say Termination Reason: Satisfiable
#eval (do
  discard <| callVampireTptp grocer_is_not_a_cyclist_hypotheses fo!{⊥} (verbose := true)
  : IO Unit)

-- Should say Termination Reason: Refutation
#eval (do
  discard <| callVampireTptp grocer_is_not_a_cyclist_hypotheses grocer_is_not_a_cyclist_conclusion (verbose := true)
  : IO Unit)

/-
Do the same for this problem.

Wolves, foxes, birds, caterpillars, and snails are animals, and there are
some of each of them.
Also there are some grains, and grains are plants.
Every animal either likes to eat all plants or all animals smaller than itself that
like to eat some plants.
Caterpillars and snails are smaller than birds,
which are smaller than foxes, which in turn are smaller than wolves.
Wolves do not like to eat foxes or grains, while birds like to eat caterpillars
but not snails.
Caterpillars and snails like to eat some plants.
Therefore there is an animal that likes to eat an animal that eats some grains.

(Some of these hypotheses are best represented with multiple formulas.)
-/

def animals_hypotheses : List FOForm := [
  -- Wolves, foxes, birds, caterpillars, and snails are animals, and there are
  -- some of each of them.
  fo!{∃ x. Animal(%x) ∧ %x = Wolf},
  fo!{∃ x. Animal(%x) ∧ %x = Fox},
  fo!{∃ x. Animal(%x) ∧ %x = Bird},
  fo!{∃ x. Animal(%x) ∧ %x = Caterpillar},
  fo!{∃ x. Animal(%x) ∧ %x = Snail},

  -- Also there are some grains, and grains are plants.
  fo!{∃ x. Plant(%x) ∧ %x = Grain},
  -- Every animal either likes to eat all plants or all animals smaller than
  -- itself that like to eat some plants.
  fo!{∀ x. Animal(%x) → (LikesToEat(%x, AllPlants) ∨
    (∀ y. Animal(%y) ∧ Smaller(%y, %x) ∧ LikesToEat(%y, SomePlants) → LikesToEat(%x, %y)))},
  -- Caterpillars and snails are smaller than birds, which are smaller than
  -- foxes, which in turn are smaller than wolves.
  fo!{∀ x. Caterpillar(%x) → (∃ y. Bird(%y) ∧ Smaller(%x, %y))},
  -- Wolves do not like to eat foxes or grains, while birds like to eat
  -- caterpillars but not snails.
  fo!{∀ x. Wolf(%x) → ¬ LikesToEat(%x, Fox)},
  -- Caterpillars and snails like to eat some plants.
  fo!{∃ x. Caterpillar(%x) ∧ LikesToEat(%x, SomePlants)}
  -- It turns out that this is not needed.
  -- fo!{∀ x. ∀ y. ∀ z. Smaller(%x, %y) ∧ Smaller(%y, %z) → Smaller(%x, %z)}
]

def animals_conclusion: FOForm :=
-- Therefore there is an animal that likes to eat an animal that eats some
-- grains.
fo!{∃ x. ∃ y. Animal(%x) ∧ Animal(%y) ∧ LikesToEat(%x, %y) ∧ LikesToEat(%y, grains)}

#eval (do
  discard <| callVampireTptp animals_hypotheses fo!{⊥} (verbose := true)
  : IO Unit)

#eval (do
  discard <| callVampireTptp animals_hypotheses animals_conclusion (verbose := true)
  : IO Unit)
