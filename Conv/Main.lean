import Conv.Char
import Conv.Locality
import Conv.Join

/-!
# Conv: the headline theorem
-/

namespace Conv

/-- The whole claim of the Conv library. -/
theorem target : target_stmt :=
  ⟨char, locality, local_iff_finite, join, conj_local⟩

end Conv
