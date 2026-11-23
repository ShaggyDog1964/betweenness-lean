/-
# Final audit

Checks that the headline result has exactly the statement type from `Statement.lean`, and prints
its axioms and those of `Q3L.lemma_H`, Lemma 34 of the working paper in general dimension
(expected: `propext`, `Classical.choice`, `Quot.sound` only). Run with
`lake env lean Q3L/Audit.lean`.
-/
import Q3L.Main

example : Q3L.target_stmt := Q3L.target

#print axioms Q3L.target
#print axioms Q3L.lemma_H
