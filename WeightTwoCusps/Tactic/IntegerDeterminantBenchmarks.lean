module

public import WeightTwoCusps.Tactic.IntegerDeterminant

/-! # Large integer determinant regression independent of cusp-form data -/

set_option maxRecDepth 4096

@[expose] public section

namespace WeightTwoCusps.IntegerDeterminantBenchmarks

/-- `I + J`, where `J` is the all-ones matrix. Its entries are computed from
indices rather than supplied as a precomputed numerical certificate. -/
def dense (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if i = j then 2 else 1

-- The determinant is 90; the search must skip 2, 3 and 5 before using 7.
-- This declaration retains the default heartbeat budget.
theorem dense_eightyNine : (dense 89).det ≠ 0 := by
  integer_det

#print axioms dense_eightyNine

end WeightTwoCusps.IntegerDeterminantBenchmarks
