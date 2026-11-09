module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(23z)^(-1) η(46z) η(69z)^2 η(138z) η(276z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(23z)^(-1) η(46z) η(69z)^2 η(138z) η(276z)^(-1)` at level 276. -/
abbrev cuspForm_276_eta_1m3_2p8_4m3_23m1_46p1_69p2_138p1_276m1 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -3, 1 => 8, 3 => -3, 22 => -1, 45 => 1, 68 => 2, 137 => 1, 275 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m3_2p8_4m3_23m1_46p1_69p2_138p1_276m1_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m3_2p8_4m3_23m1_46p1_69p2_138p1_276m1 =
    [0, 1, 3, 1, -2, 2, 1, -4, -1, -2, 0, 2, -4, -1, -2, -2, 1, 0, 2, -2,
     2, 0, -4, 1, 1, 5, 3, 3, 2, -1, -4, -1, 2, -2, 2, -4, 2, 2, -2, 1,
     2, 3, -6, 4, -2, -4, 1, 1, 7, 1, 3, 4, 2, -6, -1, 0, -4, -2, -5, 2,
     2, -2, -3, 4, 3, -2, 4, -6, -6, 1, -2, 3, 0, 5, 0, -1, 0, -6, 3, -2,
     -4, -1, 7, 4, -2, -2, 4, 1, -2, 0, -8, 0, 0, -1, 1, -2, -2, 4, 1, 0] := by
  eta_coeff

end WeightTwoCusps
