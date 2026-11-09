module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(z)^(-1) η(3z)^2 η(5z)^2 η(15z)^(-1) η(27z) η(45z)`; see
[the local level table](../../TABLE.md#level-405).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(5z)^2 η(15z)^(-1) η(27z) η(45z)` at level 405. -/
abbrev cuspForm_405_eta_1m1_3p2_5p2_15m1_27p1_45p1 : gamma0CuspForms 405 :=
  etaQuotientCuspForm 405 sparse![405; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 26 => 1, 44 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_405_eta_1m1_3p2_5p2_15m1_27p1_45p1_first_coeffs :
    first_coeffs 100 cuspForm_405_eta_1m1_3p2_5p2_15m1_27p1_45p1 =
    [0, 0, 0, 1, 1, 2, 1, 3, 1, 2, 0, 4, 1, 2, 0, 3, 0, 0, 1, 5,
     2, 2, 2, 3, 0, 0, 2, 4, 1, 0, 0, -1, -2, 1, -1, 5, -2, 4, -4, 2,
     -2, 4, -3, 4, 0, -1, -5, -2, -2, 1, -3, 4, -2, -1, -4, -1, -2, -1, -3, -2,
     -4, -5, -7, 0, -7, -2, -6, 3, -7, -3, -4, 4, -3, -6, -2, 1, -5, -3, -5, 6,
     -9, -4, -3, 7, -4, 2, -2, -1, -4, -6, -2, -1, -2, -1, -10, 1, -4, -4, -5, 4] := by
  eta_coeff

end WeightTwoCusps
