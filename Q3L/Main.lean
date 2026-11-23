/-
# Planar dichotomy: main theorem (no proof holes here)

`Q3L.target : Q3L.target_stmt`, assembled from the three parts, which are proved in the lemma
files `Q3L/*.lean`.
-/
import Q3L.Statement
import Q3L.PartI
import Q3L.PartII
import Q3L.PartIII

namespace Q3L

theorem target : target_stmt := ⟨part_i, part_ii, part_iii⟩

end Q3L
