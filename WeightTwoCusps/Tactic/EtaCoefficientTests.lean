module

public import WeightTwoCusps.Tactic.EtaCoefficient

/-! # Regression checks for signed eta-quotient coefficient evaluation -/

public section

open WeightTwoCusps WeightTwoCusps.EtaQuotient UpperHalfPlane

-- Ramanujan's discriminant, including initial vanishing and signed values.
example : (qExpansion 1 (etaQuotient 1 ![24])).coeff 0 = 0 := by simp
example : (qExpansion 1 (etaQuotient 1 ![24])).coeff 1 = 1 := by simp
example : (qExpansion 1 (etaQuotient 1 ![24])).coeff 2 = -24 := by simp
example : (qExpansion 1 (etaQuotient 1 ![24])).coeff 3 = 252 := by eta_coeff
example : (qExpansion 1 (etaQuotient 1 ![24])).coeff 4 = -1472 := by eta_coeff

theorem eta_tau_ten : (qExpansion 1 (etaQuotient 1 ![24])).coeff 10 = -115920 := by eta_coeff

-- A modular quotient with nonzero constant term and negative exponents.
example : (qExpansion 1 (etaQuotient 4 ![-8, 20, 0, -8])).coeff 0 = 1 := by simp
example : (qExpansion 1 (etaQuotient 4 ![-8, 20, 0, -8])).coeff 1 = 8 := by simp
example : (qExpansion 1 (etaQuotient 4 ![-8, 20, 0, -8])).coeff 2 = 24 := by eta_coeff
example : (qExpansion 1 (etaQuotient 4 ![-8, 20, 0, -8])).coeff 3 = 32 := by eta_coeff

-- Odd exponents, and entries at nondivisors being ignored.
example : (qExpansion 1 (etaQuotient 3 ![24, 999, 0])).coeff 3 = 252 := by simp
example : (qExpansion 1 (etaQuotient 0 (fun i ↦ Fin.elim0 i))).coeff 0 = 1 := by simp
example : (qExpansion 1 (etaQuotient 1 ![0])).coeff 5 = 0 := by simp
example : (qExpansion 1 (etaQuotient 60 (fun _ ↦ 0))).coeff 5 = 0 := by simp

-- A larger infinity shift and reciprocal Euler factors.
example : (qExpansion 1 (etaQuotient 11 ![-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22])).coeff 5 =
    0 := by simp
example : (qExpansion 1 (etaQuotient 11 ![-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22])).coeff 12 =
    5 := by eta_coeff
example : (qExpansion 1 (etaQuotient 11 ![-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22])).coeff 20 =
    481 := by eta_coeff

-- Closed definitions and both bundled constructors.
private def r15 : Fin 15 → ℤ := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

example : (qExpansion 1 (etaQuotient 15 r15)).coeff 3 = -1 := by simp
example : (qExpansion 1 (etaQuotientMF 15 r15 (k := 2))).coeff 3 = -1 := by eta_coeff
example : (qExpansion 1 (etaQuotientCuspForm 15 r15 (k := 2))).coeff 3 = -1 := by simp
example : (qExpansion 1 (etaQuotientMF 1 ![24] (k := 12))).coeff 0 = 0 := by simp

theorem eta_signed_fifteen_four :
    (qExpansion 1 (etaQuotient 15 ![-1, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])).coeff 4 =
      -2 := by eta_coeff

-- Unsupported symbolic and nonintegral infinity exponents are left alone.
example (n : ℕ) (h : (qExpansion 1 (etaQuotient 1 ![24])).coeff n = 0) :
    (qExpansion 1 (etaQuotient 1 ![24])).coeff n = 0 := by
  fail_if_success simp only [WeightTwoCusps.Tactic.etaQuotientCoeff_ofNat]
  exact h

example (h : (qExpansion 1 (etaQuotient 1 ![1])).coeff 2 = 7) :
    (qExpansion 1 (etaQuotient 1 ![1])).coeff 2 = 7 := by
  fail_if_success simp only [WeightTwoCusps.Tactic.etaQuotientCoeff_ofNat,
    WeightTwoCusps.Tactic.etaQuotientCoeff_post]
  exact h

example (h : (qExpansion 1 (etaQuotient 1 ![-24])).coeff 2 = 7) :
    (qExpansion 1 (etaQuotient 1 ![-24])).coeff 2 = 7 := by
  fail_if_success simp only [WeightTwoCusps.Tactic.etaQuotientCoeff_ofNat,
    WeightTwoCusps.Tactic.etaQuotientCoeff_post]
  exact h

example (r : Fin 1 → ℤ) (h : (qExpansion 1 (etaQuotient 1 r)).coeff 2 = 7) :
    (qExpansion 1 (etaQuotient 1 r)).coeff 2 = 7 := by
  fail_if_success simp only [WeightTwoCusps.Tactic.etaQuotientCoeff_ofNat,
    WeightTwoCusps.Tactic.etaQuotientCoeff_post]
  exact h

#print axioms WeightTwoCusps.EtaQuotient.qExpansion_coeff_eq_coefficient
#print axioms WeightTwoCusps.EtaQuotient.inverseCoefficient_table
#print axioms eta_tau_ten
#print axioms eta_signed_fifteen_four
