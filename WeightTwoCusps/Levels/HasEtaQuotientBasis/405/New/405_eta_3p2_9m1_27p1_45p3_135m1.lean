module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(3z)^2 η(9z)^(-1) η(27z) η(45z)^3 η(135z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z)^2 η(9z)^(-1) η(27z) η(45z)^3 η(135z)^(-1)` at level 405. -/
abbrev cuspForm_405_eta_3p2_9m1_27p1_45p3_135m1 : gamma0CuspForms 405 :=
  etaQuotientCuspForm 405 sparse![405; 2 => 2, 8 => -1, 26 => 1, 44 => 3, 134 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_405_eta_3p2_9m1_27p1_45p3_135m1_first_coeffs :
    first_coeffs 100 cuspForm_405_eta_3p2_9m1_27p1_45p3_135m1 =
    [0, 1, 0, 0, -2, 0, 0, -1, 0, 0, 3, 0, 0, -1, 0, 0, 1, 0, 0, 2,
     0, 0, -3, 0, 0, -2, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0,
     -3, 0, 0, -1, 0, 0, 0, 0, 0, 6, 0, 0, 5, 0, 0, -6, 0, 0, 0, 0,
     0, -4, 0, 0, -5, 0, 0, 8, 0, 0, 3, 0, 0, -4, 0, 0, -1, 0, 0, -1,
     0, 0, -3, 0, 0, 9, 0, 0, 6, 0, 0, -8, 0, 0, -3, 0, 0, -7, 0, 0] := by
  eta_coeff

end WeightTwoCusps
