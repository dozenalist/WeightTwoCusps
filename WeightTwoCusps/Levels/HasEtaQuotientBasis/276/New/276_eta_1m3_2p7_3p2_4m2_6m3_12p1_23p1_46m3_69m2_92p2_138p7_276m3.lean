module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(12z) η(23z) η(46z)^(-3) η(69z)^(-2) η(92z)^2 η(138z)^7 η(276z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(12z) η(23z) η(46z)^(-3) η(69z)^(-2) η(92z)^2 η(138z)^7 η(276z)^(-3)` at level 276. -/
abbrev cuspForm_276_eta_1m3_2p7_3p2_4m2_6m3_12p1_23p1_46m3_69m2_92p2_138p7_276m3 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 11 => 1, 22 => 1, 45 => -3, 68 => -2, 91 => 2, 137 => 7, 275 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m3_2p7_3p2_4m2_6m3_12p1_23p1_46m3_69m2_92p2_138p7_276m3_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m3_2p7_3p2_4m2_6m3_12p1_23p1_46m3_69m2_92p2_138p7_276m3 =
    [0, 0, 0, 1, 3, 2, -1, -2, -2, 1, 2, 0, -2, -7, -2, 2, 0, 2, -3, -2,
     -2, 0, 6, 0, -1, -2, -1, -1, 0, 5, 2, -1, -3, 0, 2, 4, 7, 2, -4, 3,
     8, 3, 0, 0, 0, -4, 0, 3, -1, -4, 4, 2, -4, -2, -3, 2, 0, 0, -3, -12,
     -6, 6, -7, -6, -4, -2, -2, -10, 8, 1, -2, -1, 5, -3, 0, 9, 0, 0, -5, 4,
     0, 4, 7, 6, -10, 4, 18, 3, 0, -2, 6, 0, -1, 3, 7, -6, 8, 2, -6, 2] := by
  eta_coeff

end WeightTwoCusps
