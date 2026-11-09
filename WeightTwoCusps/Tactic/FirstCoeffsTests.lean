module

public import WeightTwoCusps.Tactic.EtaCoefficient

/-! # Regression checks for batched q-expansion coefficient lists -/

@[expose] public section

open WeightTwoCusps UpperHalfPlane

namespace WeightTwoCusps.FirstCoeffsTests

example (f : ℍ → ℂ) : first_coeffs 0 f = [] := rfl
example (f : ℍ → ℂ) : first_coeffs 2 f =
    [(qExpansion 1 f).coeff 0, (qExpansion 1 f).coeff 1] := rfl
example (f : ℍ → ℂ) : (first_coeffs 50 f).length = 50 := by simp

def r11 : Fin 11 → ℤ := ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]

/-- Degrees 0 through 49 of the classical level-eleven eta product. -/
def levelElevenFirstFifty : List ℂ :=
  [0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0,
   2, 2, -2, -1, 0, -4, -8, 5, -4, 0, 2, 7, 8, -1, 4, -2, -4, 3, 0, -4,
   0, -8, -4, -6, 2, -2, 2, 8, 4, -3]

theorem raw_first_fifty : first_coeffs 50 (etaQuotient 11 r11) =
    levelElevenFirstFifty := by
  unfold levelElevenFirstFifty
  eta_coeff

theorem modular_first_fifty : first_coeffs 50 (etaQuotientMF 11 r11 (k := 2)) =
    levelElevenFirstFifty := by
  unfold levelElevenFirstFifty
  eta_coeff

theorem cusp_first_fifty : first_coeffs 50 (etaQuotientCuspForm 11 r11 (k := 2)) =
    levelElevenFirstFifty := by
  unfold levelElevenFirstFifty
  eta_coeff

-- List literals and ordinary simplification.
example : first_coeffs 5 (etaQuotient 1 ![24]) = [0, 1, -24, 252, -1472] := by eta_coeff
example : first_coeffs 5 (etaQuotient 1 ![24]) = [0, 1, -24, 252, -1472] := by simp

-- Nonzero constant coefficients, negative and odd exponents, and ignored entries.
example : first_coeffs 4 (etaQuotient 4 ![-8, 20, 0, -8]) = [1, 8, 24, 32] := by eta_coeff
example : first_coeffs 5 (etaQuotient 3 ![24, 999, 0]) = [0, 1, -24, 252, -1472] := by
  eta_coeff
example : first_coeffs 4
    (etaQuotient 15 ![1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) = [0, 1, -1, -1] := by
  eta_coeff

-- Precision may end before the leading term, or include it as the last entry.
example : first_coeffs 3 (etaQuotient 1 ![120]) = [0, 0, 0] := by eta_coeff
example : first_coeffs 5 (etaQuotient 1 ![120]) = [0, 0, 0, 0, 0] := by eta_coeff
example : first_coeffs 6 (etaQuotient 1 ![120]) = [0, 0, 0, 0, 0, 1] := by eta_coeff
-- A huge vanishing order must not allocate its entire leading-zero table.
example : first_coeffs 3 (etaQuotient 1 ![24000000]) = [0, 0, 0] := by eta_coeff
example : first_coeffs 3 (etaQuotient 0 (fun i ↦ Fin.elim0 i)) = [1, 0, 0] := by eta_coeff
example (f : ℍ → ℂ) : first_coeffs 0 f = [] := by eta_coeff

-- Symbolic and unsupported infinity orders are left unchanged; false lists fail.
example (r : Fin 1 → ℤ) (h : first_coeffs 3 (etaQuotient 1 r) = [1, 2, 3]) :
    first_coeffs 3 (etaQuotient 1 r) = [1, 2, 3] := by
  fail_if_success eta_coeff
  exact h

example (h : first_coeffs 3 (etaQuotient 1 ![1]) = [1, 2, 3]) :
    first_coeffs 3 (etaQuotient 1 ![1]) = [1, 2, 3] := by
  fail_if_success eta_coeff
  exact h

example (h : first_coeffs 3 (etaQuotient 1 ![-24]) = [1, 2, 3]) :
    first_coeffs 3 (etaQuotient 1 ![-24]) = [1, 2, 3] := by
  fail_if_success eta_coeff
  exact h

example : True := by
  fail_if_success
    have : first_coeffs 3 (etaQuotient 1 ![24]) = [0, 1, 24] := by eta_coeff
  trivial

#print axioms WeightTwoCusps.EtaQuotient.first_coeffs_eq_of_table
#print axioms raw_first_fifty
#print axioms modular_first_fifty
#print axioms cusp_first_fifty

end WeightTwoCusps.FirstCoeffsTests
