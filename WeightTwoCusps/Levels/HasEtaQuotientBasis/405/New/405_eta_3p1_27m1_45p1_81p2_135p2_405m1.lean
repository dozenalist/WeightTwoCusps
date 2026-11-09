module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(3z) η(27z)^(-1) η(45z) η(81z)^2 η(135z)^2 η(405z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z) η(27z)^(-1) η(45z) η(81z)^2 η(135z)^2 η(405z)^(-1)` at level 405. -/
abbrev cuspForm_405_eta_3p1_27m1_45p1_81p2_135p2_405m1 : gamma0CuspForms 405 :=
  etaQuotientCuspForm 405 sparse![405; 2 => 1, 26 => -1, 44 => 1, 80 => 2, 134 => 2, 404 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_405_eta_3p1_27m1_45p1_81p2_135p2_405m1_first_coeffs :
    first_coeffs 100 cuspForm_405_eta_3p1_27m1_45p1_81p2_135p2_405m1 =
    [0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0,
     0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, -2,
     0, 0, -3, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 3, 0, 0,
     2, 0, 0, 2, 0, 0, -1, 0, 0, -2, 0, 0, -2, 0, 0, 1, 0, 0, 2, 0] := by
  eta_coeff

end WeightTwoCusps
