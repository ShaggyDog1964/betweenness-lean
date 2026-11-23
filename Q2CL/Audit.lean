/-
# Final audit

Checks that the headline results have exactly the statement types from `Statement.lean`, and
prints their axioms (expected: `propext`, `Classical.choice`, `Quot.sound` only). Run with
`lake env lean Q2CL/Audit.lean`.
-/
import Q2CL.Main

example : Q2CL.target_stmt := Q2CL.target
example : Q2CL.lower_stmt := Q2CL.lower
example : Q2CL.upper_stmt := Q2CL.upper

#print axioms Q2CL.target
#print axioms Q2CL.lower
#print axioms Q2CL.upper
