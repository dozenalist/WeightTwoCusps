module

public import WeightTwoCusps.Tactic.EtaCoefficient

/-! # Coefficients and finite tables of rescaled cusp forms -/

@[expose] public noncomputable section

open WeightTwoCusps UpperHalfPlane

namespace WeightTwoCusps.RescaleCoefficientTests

abbrev f11 : gamma0CuspForms 11 :=
  etaQuotientCuspForm 11 ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]

abbrev g22 : gamma0CuspForms 22 := gamma0Rescale f11 2

def namedLift : gamma0CuspForms 22 := gamma0Rescale f11 2

def namedSource : gamma0CuspForms 11 := f11

-- Constant, leading, missing, signed, and later coefficients.
example : (qExpansion 1 g22).coeff 0 = 0 := by eta_coeff
example : (qExpansion 1 g22).coeff 1 = 0 := by eta_coeff
example : (qExpansion 1 g22).coeff 2 = 1 := by eta_coeff
example : (qExpansion 1 g22).coeff 4 = -2 := by eta_coeff
example : (qExpansion 1 g22).coeff 6 = -1 := by eta_coeff
example : (qExpansion 1 g22).coeff 50 = -4 := by eta_coeff
example : (qExpansion 1 namedLift).coeff 4 = -2 := by eta_coeff
example : (qExpansion 1 (gamma0Rescale namedSource 2)).coeff 4 = -2 := by eta_coeff

theorem lifted_prefix : first_coeffs 12 g22 = [0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0] := by
  eta_coeff

theorem lifted_first_fifty : first_coeffs 50 g22 =
    [0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 2, 0, -2, 0, 0, 0, -2, 0,
     -2, 0, 1, 0, -2, 0, 4, 0, 4, 0, -1, 0, -4, 0, -2, 0, 4, 0, 0, 0,
     2, 0, 2, 0, -2, 0, -1, 0, 0, 0] := by eta_coeff

example : first_coeffs 0 g22 = [] := by eta_coeff
example : first_coeffs 1 g22 = [0] := by eta_coeff
example : first_coeffs 3 g22 = [0, 0, 1] := by eta_coeff
example : first_coeffs 8 namedLift = [0, 0, 1, 0, -2, 0, -1, 0] := by eta_coeff
example : first_coeffs 5 (gamma0Rescale f11 5) = [0, 0, 0, 0, 0] := by eta_coeff
example : first_coeffs 6 (gamma0Rescale f11 5) = [0, 0, 0, 0, 0, 1] := by eta_coeff

-- Ambient levels and restriction do not alter coefficients or prefixes.
example : (qExpansion 1 (gamma0RescaleToLevel f11 2 (by decide : 22 ∣ 44))).coeff 4 = -2 := by
  eta_coeff
example : first_coeffs 8 (gamma0RescaleToLevel f11 2 (by decide : 22 ∣ 44)) =
    [0, 0, 1, 0, -2, 0, -1, 0] := by eta_coeff
example : first_coeffs 8 (gamma0Restrict g22 (by decide : 22 ∣ 44)) =
    [0, 0, 1, 0, -2, 0, -1, 0] := by eta_coeff
example : (qExpansion 1 (gamma0Restrict g22 (by decide : 22 ∣ 44))).coeff 4 = -2 := by
  eta_coeff

-- The linear-map variants expose the same rescaling.
example : (qExpansion 1 ((gamma0Rescaleₗ 2) f11)).coeff 4 = -2 := by eta_coeff
example : first_coeffs 8 ((gamma0RescaleToLevelₗ 2 (by decide : 22 ∣ 44)) f11) =
    [0, 0, 1, 0, -2, 0, -1, 0] := by eta_coeff

-- Repeated lifts compose without losing the zero insertion pattern.
example : (qExpansion 1 (gamma0Rescale g22 3)).coeff 12 = -2 := by eta_coeff
example : (qExpansion 1 (gamma0Rescale g22 3)).coeff 13 = 0 := by eta_coeff
example (f : gamma0CuspForms 11) :
    (qExpansion 1 (gamma0Rescale f 2)).coeff 3 = 0 := by eta_coeff
example : first_coeffs 15 (gamma0Rescale g22 3) =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0] := by eta_coeff

-- Periods are measured relative to the original source form.
example : (qExpansion 2 g22).coeff 2 = 0 := by eta_coeff
example : (qExpansion 2 g22).coeff 4 = 1 := by eta_coeff
example : (qExpansion 2 g22).coeff 8 = -2 := by eta_coeff
example : (qExpansion 2 f11).coeff 4 = -2 := by eta_coeff
example : (qExpansion (1 / 2) g22).coeff 1 = 1 := by eta_coeff
example : (qExpansion (1 / 2) g22).coeff 2 = -2 := by eta_coeff
example : (qExpansion (1 + 1 / 2) g22).coeff 6 = -2 := by eta_coeff
theorem nested_fractional_period :
    (qExpansion (1 / 6) (gamma0Rescale g22 3)).coeff 2 = -2 := by eta_coeff

-- False answers and periods outside the supported arithmetic are not certified.
example : True := by
  fail_if_success
    have : (qExpansion 1 g22).coeff 4 = 2 := by eta_coeff
  fail_if_success
    have : first_coeffs 5 g22 = [0, 0, 1, 0, 2] := by eta_coeff
  fail_if_success
    have : (qExpansion 0 g22).coeff 2 = 7 := by eta_coeff
  fail_if_success
    have : (qExpansion (-1) g22).coeff 2 = 7 := by eta_coeff
  fail_if_success
    have : (qExpansion (1 / 3) g22).coeff 1 = 7 := by eta_coeff
  trivial

#print axioms gamma0Rescale_qExpansion
#print axioms gamma0Rescale_qExpansion_period
#print axioms gamma0Rescale_first_coeffs
#print axioms lifted_prefix
#print axioms lifted_first_fifty
#print axioms nested_fractional_period

end WeightTwoCusps.RescaleCoefficientTests
