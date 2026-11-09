module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(3z) η(4z) η(6z) η(12z)^(-1) η(69z) η(92z) η(138z) η(276z)^(-1)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(4z) η(6z) η(12z)^(-1) η(69z) η(92z) η(138z) η(276z)^(-1)` at level 276. -/
abbrev cuspForm_276_eta_3p1_4p1_6p1_12m1_69p1_92p1_138p1_276m1 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 2 => 1, 3 => 1, 5 => 1, 11 => -1, 68 => 1, 91 => 1, 137 => 1, 275 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_3p1_4p1_6p1_12m1_69p1_92p1_138p1_276m1_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_3p1_4p1_6p1_12m1_69p1_92p1_138p1_276m1 =
    [0, 1, 0, 0, -1, -1, 0, -2, 1, -1, 1, 2, 1, 1, -1, 2, 1, -1, -1, -1,
     -1, 0, 1, 1, -2, 2, -1, -1, -2, -1, 0, -2, 1, -1, 0, 0, 3, 1, 1, 1,
     -1, 0, 1, -1, 2, 1, 0, 0, -1, 2, 1, -1, 0, -1, 0, -1, -1, -2, 1, 1,
     0, 1, -2, 2, 0, -2, -2, 1, -1, 0, -2, 1, -1, 1, 0, -1, 1, -1, 2, -2,
     -1, -1, 0, 2, 0, -2, 1, 3, 3, 3, -1, -2, -1, 2, 0, 1, 1, 4, 1, 2] := by
  eta_coeff

end WeightTwoCusps
