module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(5z)^3 η(6z)^(-2) η(8z)^(-1) η(10z)^(-3) η(15z)^(-1) η(20z)^3 η(24z) η(30z) η(40z)^(-1) η(60z)^(-1) η(120z)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(5z)^3 η(6z)^(-2) η(8z)^(-1) η(10z)^(-3) η(15z)^(-1) η(20z)^3 η(24z) η(30z) η(40z)^(-1) η(60z)^(-1) η(120z)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p6_3p1_5p3_6m2_8m1_10m3_15m1_20p3_24p1_30p1_40m1_60m1_120p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 6, 2 => 1, 4 => 3, 5 => -2, 7 => -1, 9 => -3, 14 => -1, 19 => 3, 23 => 1, 29 => 1, 39 => -1, 59 => -1, 119 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p6_3p1_5p3_6m2_8m1_10m3_15m1_20p3_24p1_30p1_40m1_60m1_120p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p6_3p1_5p3_6m2_8m1_10m3_15m1_20p3_24p1_30p1_40m1_60m1_120p1 =
    [0, 0, 0, 0, 1, 3, 3, 3, 3, -3, -6, -3, -5, -3, 6, 3, -3, 3, 0, -6,
     -1, 0, -6, -6, 3, -3, -6, 0, -4, -3, 3, 6, 3, 3, -6, 3, 13, 3, 12, 3,
     -3, 0, 6, 12, 0, 0, 0, 0, -3, 12, 18, -3, 2, 3, 3, -15, -12, 0, -18, 9,
     5, -6, -12, -9, -3, -9, 6, -6, 6, -3, -6, 6, 3, -6, -18, -3, -4, -12, -12, -6,
     3, 6, 24, 6, -16, 9, -12, -3, 0, -6, -6, -6, 0, 6, 12, 6, 3, -12, 24, 9] := by
  eta_coeff

end WeightTwoCusps
