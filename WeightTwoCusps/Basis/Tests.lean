module

public import WeightTwoCusps.Basis

/-! # Regression checks for coefficient-certified cusp-form bases -/

@[expose] public section

noncomputable section

open WeightTwoCusps WeightTwoCusps.Tactic Module UpperHalfPlane

namespace WeightTwoCusps.BasisTests

def r11 : Fin 11 → ℤ := sparse![11; 0 => 2, 10 => 2]
def r22 : Fin 22 → ℤ := sparse![22; 0 => 2, 10 => 2]
def s22 : Fin 22 → ℤ := sparse![22; 1 => 2, 21 => 2]
def r33 : Fin 33 → ℤ := sparse![33; 0 => 2, 10 => 2]
def s33 : Fin 33 → ℤ := sparse![33; 0 => 1, 2 => 1, 10 => 1, 32 => 1]
def t33 : Fin 33 → ℤ := sparse![33; 2 => 2, 32 => 2]

/-- All arithmetic, dimension and coefficient proofs are omitted. -/
def levelElevenBasis : Basis (Fin 1) ℂ (gamma0CuspForms 11) :=
  etaQuotientBasis 11 ![r11]

-- Normalized uniqueness uses the general dimension-one theorem.
theorem levelEleven_normalized_unique :
    ∃! f : gamma0CuspForms 11, (qExpansion 1 f).coeff 1 = 1 := by
  exact existsUnique_normalized_of_finrank_eq_one one_pos (by simp) (by cusp_basis)
    (etaQuotientCuspForm 11 r11) 1 (by eta_coeff)

/-- The two degeneracy forms from level eleven form the level-22 basis. -/
def levelTwentyTwoBasis : Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  etaQuotientBasis 22 ![r22, s22]

-- A three-dimensional example, including odd exponents.
def levelThirtyThreeBasis : Basis (Fin 3) ℂ (gamma0CuspForms 33) :=
  etaQuotientBasis 33 ![r33, s33, t33]

example : levelTwentyTwoBasis 0 = etaQuotientCuspForm 22 r22 := by
  simp [levelTwentyTwoBasis]

example : levelTwentyTwoBasis 1 = etaQuotientCuspForm 22 s22 := by
  simp [levelTwentyTwoBasis]

-- An actual vector of bundled eta quotients is accepted directly.
example : Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  cuspFormBasis ![etaQuotientCuspForm 22 r22, etaQuotientCuspForm 22 s22]

-- Reverse the rows, so the coefficient table is no longer upper triangular.
example : Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  etaQuotientBasis 22 ![s22, r22]

-- Selected coefficients may extend beyond the dimension; the determinant is -2.
example : Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  etaQuotientBasis 22 ![r22, s22] (c := ![1, 4])

theorem levelTwentyTwo_independent :
    LinearIndependent ℂ ![etaQuotientCuspForm 22 r22 (k := 2),
      etaQuotientCuspForm 22 s22 (k := 2)] := by
  cusp_basis

example : LinearIndependent ℂ ![etaQuotientCuspForm 22 r22 (k := 2),
    etaQuotientCuspForm 22 s22 (k := 2)] := by
  cusp_basis using ![1, 4]

-- The empty vector is a basis precisely when the space has dimension zero.
example : Basis (Fin 0) ℂ (gamma0CuspForms 1) :=
  etaQuotientBasis 1 ![]

-- Dependence and the wrong dimension must not be certified.
example : True := by
  fail_if_success
    have : LinearIndependent ℂ ![etaQuotientCuspForm 22 r22 (k := 2),
        etaQuotientCuspForm 22 r22 (k := 2)] := by cusp_basis
  fail_if_success
    have : Module.finrank ℂ (gamma0CuspForms 22) = 1 := by cusp_basis
  trivial

#print axioms WeightTwoCusps.linearIndependent_of_qExpansionMatrix_det_ne_zero
#print axioms WeightTwoCusps.basisOfQExpansionMatrix
#print axioms levelElevenBasis
#print axioms levelEleven_normalized_unique
#print axioms levelTwentyTwoBasis
#print axioms levelThirtyThreeBasis
#print axioms levelTwentyTwo_independent

end WeightTwoCusps.BasisTests
