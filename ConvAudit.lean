/-
# Audit of the Conv and Q1 developments

Checks that the general convexity theorem and the two-attribute example have exactly the
statement types of `Conv/Statement.lean` and `Q1/Statement.lean`, and prints their
axioms (expected: `propext`, `Classical.choice`, `Quot.sound` only). It sits at the top
level, outside the `Conv` and `Q1` globs, so `lake build` does not build it. Run with
`lake env lean ConvAudit.lean`.
-/
import Conv
import Q1.ConvMain
import Q1.Main

example : Conv.target_stmt := Conv.target
example : Q1.target_stmt := Q1.target_via_conv

#print axioms Conv.target
#print axioms Q1.target_via_conv

-- The direct proof of the two-attribute example, without Conv.
example : Q1.target_stmt := Q1.target
#print axioms Q1.target
