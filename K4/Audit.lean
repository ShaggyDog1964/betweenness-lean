/-
# Final audit

Checks that the headline result has exactly the statement type from `Statement.lean`, and prints
the axioms of the main results (expected: `propext`, `Classical.choice`, `Quot.sound` only).
Not imported by `K4.lean`; run with `lake env lean K4/Audit.lean`.
-/
import K4

example : K4.target_stmt := K4.target

#print axioms K4.target
#print axioms K4.logCert_exists
#print axioms K4.representable_of_chain
