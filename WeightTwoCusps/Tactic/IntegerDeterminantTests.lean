module

public import WeightTwoCusps.Tactic.IntegerDeterminant

/-! # General regressions for integer determinant certificates -/

@[expose] public section

namespace WeightTwoCusps.IntegerDeterminantTests

theorem empty : (Matrix.of ![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
  integer_det

theorem negative_triangular : (!![(-3 : ℤ), 0, 0; 4, 2, 0; 1, 7, -5]).det ≠ 0 := by
  integer_det

theorem swapped : (!![(0 : ℤ), 1, 2; 1, 0, 3; 0, 0, 1]).det ≠ 0 := by
  integer_det

-- The determinant is 30, so 2, 3 and 5 are bad primes and 7 succeeds.
theorem several_bad_primes : (!![(1 : ℤ), 1; 1, 31]).det ≠ 0 := by
  integer_det

def dense (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if i = j then 2 else 1

theorem named_dense : (dense 12).det ≠ 0 := by
  integer_det

-- A local alias and reducible arithmetic entries are normalized first.
example : True := by
  let A := (!![(1 + 1 : ℤ), 1; 1, -2 * 3])
  have : A.det ≠ 0 := by integer_det
  trivial

set_option integer_det.maxPrimes 3 in
example : True := by
  fail_if_success
    have : (!![(1 : ℤ), 1; 1, 31]).det ≠ 0 := by integer_det
  fail_if_success
    have : (!![(1 : ℤ), 2; 2, 4]).det ≠ 0 := by integer_det
  fail_if_success
    have : (!![(1 : ℤ), 0; 0, 0]).det ≠ 0 := by integer_det
  trivial

-- Soundness needs no prime-modulus hypothesis, and the algebraic transport
-- theorem works with any finite index type and characteristic-zero ring.
example : (Mathlib.Tactic.Matrix.ofLists 2 2 [[1, 0], [0, 1]] :
    Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 :=
  matrix_det_ne_zero_of_modularUpperCheck 4 2 (by decide)
    [[1, 0], [0, 1]] [[1, 0], [0, 1]] (by decide)

example {K ι : Type*} [CommRing K] [CharZero K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) : (A.map (fun z ↦ (z : K))).det ≠ 0 ↔ A.det ≠ 0 :=
  matrix_det_intCast_iff A

#print axioms empty
#print axioms negative_triangular
#print axioms swapped
#print axioms several_bad_primes
#print axioms named_dense
#print axioms matrix_det_ne_zero_of_modularUpperCheck
#print axioms matrix_det_ne_zero_of_int_rowScale

end WeightTwoCusps.IntegerDeterminantTests
