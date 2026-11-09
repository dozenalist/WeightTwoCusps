module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 135

The eta expression is `η(15z) η(27z)^2 η(45z)^2 η(135z)^(-1)`; see
[the local level table](../../TABLE.md#level-135).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(15z) η(27z)^2 η(45z)^2 η(135z)^(-1)` at level 135. -/
abbrev cuspForm_135_eta_15p1_27p2_45p2_135m1 : gamma0CuspForms 135 :=
  etaQuotientCuspForm 135 sparse![135; 14 => 1, 26 => 2, 44 => 2, 134 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_135_eta_15p1_27p2_45p2_135m1_first_coeffs :
    first_coeffs 100 cuspForm_135_eta_15p1_27p2_45p2_135m1 =
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 2, 0,
     0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 3, 0, 0, 0,
     0, 0, 2, 0, 0, 1, 0, 0, -4, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
