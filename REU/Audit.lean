/-
# Final audit

Checks that the three headline results have exactly the statement types from
`Statement.lean`, and prints their axioms (expected: `propext`, `Classical.choice`,
`Quot.sound` only). Not imported by `REU.lean` (to keep `lake build` output free of
`#print` noise); run with `lake env lean REU/Audit.lean`.
-/
import REU

example : REU.thm1_stmt := REU.thm1
example : REU.thm1_reu_stmt := REU.thm1_reu
example : REU.bridge_stmt := REU.bridge
example : REU.bridge_stmt.{0} := REU.bridge.{0}
example : REU.bridge_stmt.{3} := REU.bridge.{3}

#print axioms REU.thm1
#print axioms REU.thm1_reu
#print axioms REU.bridge

-- Witness that random betweenness is strictly larger than random EU (`REU/Witness.lean`).
#print axioms REU.witness_CD_B_not_CDAll
#print axioms REU.witness_btw_not_EU
#print axioms REU.btw_strictly_larger_than_EU
