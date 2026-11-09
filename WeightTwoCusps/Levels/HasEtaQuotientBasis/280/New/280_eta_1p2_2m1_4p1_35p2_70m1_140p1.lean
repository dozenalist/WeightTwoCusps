module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(z)^2 η(2z)^(-1) η(4z) η(35z)^2 η(70z)^(-1) η(140z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(4z) η(35z)^2 η(70z)^(-1) η(140z)` at level 280. -/
abbrev cuspForm_280_eta_1p2_2m1_4p1_35p2_70m1_140p1 : gamma0CuspForms 280 :=
  etaQuotientCuspForm 280 sparse![280; 0 => 2, 1 => -1, 3 => 1, 34 => 2, 69 => -1, 139 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_280_eta_1p2_2m1_4p1_35p2_70m1_140p1_first_coeffs :
    first_coeffs 100 cuspForm_280_eta_1p2_2m1_4p1_35p2_70m1_140p1 =
    [0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 1, 2, 0, 0, -3, 0, 0, 0, -2, 2,
     0, 0, 2, 2, 0, 0, -1, -2, 0, 0, 0, -2, 0, 0, 1, -2, 0, 0, 2, 2,
     0, -2, 8, -2, 0, -2, -6, 0, 0, 6, 0, -2, 0, 4, -5, 0, 0, -4, -6, 0,
     0, 2, 6, 4, 0, 0, 3, 2, 0, -2, 4, 0, 0, -4, -6, 0, 0, -8, 2, 2,
     0, 4, -2, -2, 0, 0, 4, -2, 0, 2, 0, 4, 0, 4, 1, 0, 0, -4, -4, 0] := by
  eta_coeff

end WeightTwoCusps
