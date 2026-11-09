module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z) η(6z)^(-3) η(10z)^(-5) η(12z)^2 η(20z)^9 η(30z)^2 η(40z)^(-3) η(60z)^(-3) η(120z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z) η(6z)^(-3) η(10z)^(-5) η(12z)^2 η(20z)^9 η(30z)^2 η(40z)^(-3) η(60z)^(-3) η(120z)` at level 240. -/
abbrev cuspForm_240_eta_1m4_2p10_3p1_4m4_5p1_6m3_10m5_12p2_20p9_30p2_40m3_60m3_120p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => 1, 5 => -3, 9 => -5, 11 => 2, 19 => 9, 29 => 2, 39 => -3, 59 => -3, 119 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m4_2p10_3p1_4m4_5p1_6m3_10m5_12p2_20p9_30p2_40m3_60m3_120p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m4_2p10_3p1_4m4_5p1_6m3_10m5_12p2_20p9_30p2_40m3_60m3_120p1 =
    [0, 1, 4, 4, -1, 0, 3, -2, 0, 5, 1, 4, 14, 12, -4, -1, 9, -8, 0, 18,
     4, 4, 10, 4, -3, -5, -2, -8, -2, 14, 6, -6, -12, -18, 2, -6, -25, 4, -8, -16,
     3, -12, -18, -24, -6, 4, -14, 4, -6, -33, -8, 6, -8, -12, -15, 10, 6, -8, 10, -28,
     -17, 12, 4, 14, -3, 4, 6, 4, 12, 0, -4, -12, 0, 22, 18, -2, 16, 16, 0, 26,
     6, -13, -24, 8, 34, -8, 10, 6, -6, 6, -3, -12, -12, 4, 10, 2, 9, 18, -12, -12] := by
  eta_coeff

end WeightTwoCusps
