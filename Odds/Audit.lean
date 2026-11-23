/-
# Final audit

Checks that the headline result has exactly the statement type from `Statement.lean`, and prints
its axioms (expected: `propext`, `Classical.choice`, `Quot.sound` only). Run with
`lake env lean Odds/Audit.lean`.
-/
import Odds.Main

example : Odds.target_stmt := Odds.target

#print axioms Odds.target
