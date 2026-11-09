module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(23z)^(-2) η(46z)^3 η(69z)^3 η(92z)^(-1) η(138z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(23z)^(-2) η(46z)^3 η(69z)^3 η(92z)^(-1) η(138z)^(-1)` at level 276. -/
abbrev cuspForm_276_eta_1m4_2p10_3p1_4m4_6m2_12p1_23m2_46p3_69p3_92m1_138m1 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 22 => -2, 45 => 3, 68 => 3, 91 => -1, 137 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m4_2p10_3p1_4m4_6m2_12p1_23m2_46p3_69p3_92m1_138m1_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m4_2p10_3p1_4m4_6m2_12p1_23m2_46p3_69p3_92m1_138m1 =
    [0, 0, 0, 1, 4, 4, -1, 0, 4, 1, 0, 0, 2, 4, -4, -2, 0, -4, 1, 0,
     4, 0, -8, 0, -1, 0, 2, 6, 8, -2, 0, 4, -2, -2, 0, 0, 8, -8, -8, 3,
     -8, 2, -2, 8, 0, -14, 0, -6, 1, -6, 4, 8, -2, 4, -2, -6, -8, -2, 0, 12,
     -10, -12, 6, -8, 2, -4, 8, 0, -8, 1, -10, 2, -15, 0, 8, 1, 8, -12, -5, -12,
     -8, 3, 12, -4, -10, 14, -4, -1, -4, 4, 4, 4, 2, -9, 6, -16, -2, 8, 8, 6] := by
  eta_coeff

end WeightTwoCusps
