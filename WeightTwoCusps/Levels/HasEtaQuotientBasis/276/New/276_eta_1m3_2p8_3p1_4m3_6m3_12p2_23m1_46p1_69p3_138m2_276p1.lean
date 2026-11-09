module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(23z)^(-1) η(46z) η(69z)^3 η(138z)^(-2) η(276z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(23z)^(-1) η(46z) η(69z)^3 η(138z)^(-2) η(276z)` at level 276. -/
abbrev cuspForm_276_eta_1m3_2p8_3p1_4m3_6m3_12p2_23m1_46p1_69p3_138m2_276p1 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 22 => -1, 45 => 1, 68 => 3, 137 => -2, 275 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m3_2p8_3p1_4m3_6m3_12p2_23m1_46p1_69p3_138m2_276p1_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m3_2p8_3p1_4m3_6m3_12p2_23m1_46p1_69p3_138m2_276p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, -3, -1, 0, 0, 3, -1, -3,
     -2, -3, 1, 0, -1, 0, -1, 0, 0, 3, 1, -3, 1, 4, 2, 1, -2, -1, 0, -3,
     5, -1, -2, 1, -3, 4, 0, 2, -1, -1, 2, 0, 4, -2, -3, 1, 3, -1, 1, -5,
     -2, 3, -3, 8, -2, -2, 2, -3, 5, 0, -1, -1, -1, -1, -1, 4, -3, -6, 0, 4,
     -6, -4, 1, -3, 3, -3, 2, 3, 3, 3, 1, 6, 0, 1, 0, -2, -1, 2, -1, -5] := by
  eta_coeff

end WeightTwoCusps
