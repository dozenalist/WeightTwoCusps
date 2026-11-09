module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-2) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(23z)^2 η(46z)^(-3) η(69z)^(-3) η(92z) η(138z)^7 η(276z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(23z)^2 η(46z)^(-3) η(69z)^(-3) η(92z) η(138z)^7 η(276z)^(-2)` at level 276. -/
abbrev cuspForm_276_eta_1m2_2p7_3p1_4m3_6m3_12p2_23p2_46m3_69m3_92p1_138p7_276m2 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -2, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 22 => 2, 45 => -3, 68 => -3, 91 => 1, 137 => 7, 275 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m2_2p7_3p1_4m3_6m3_12p2_23p2_46m3_69m3_92p1_138p7_276m2_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m2_2p7_3p1_4m3_6m3_12p2_23p2_46m3_69m3_92p1_138p7_276m2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, -2, -5, 0, 2, 2, 2, -2, -1, -2,
     0, 6, 2, 0, -2, -2, 2, 1, 0, -2, -6, -2, 2, -4, 4, 8, -2, -6, -4, 5,
     6, 2, 2, -2, -10, -2, 0, 2, 4, -8, 0, 2, 6, 12, 1, -6, 6, 2, -6, 4,
     6, 2, -14, -8, 0, -4, -6, 6, 2, 0, 2, -6, 11, -2, -2, -2, -10, 0, 7, -8,
     -8, 3, -2, -2, -4, 16, 8, 1, 6, 14, 2, -4, 0, -1, 8, -10, 1, 0, -6, 4] := by
  eta_coeff

end WeightTwoCusps
