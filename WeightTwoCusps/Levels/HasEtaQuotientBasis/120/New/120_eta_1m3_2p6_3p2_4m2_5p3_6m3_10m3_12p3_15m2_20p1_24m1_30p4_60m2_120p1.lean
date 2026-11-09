module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z)^3 η(15z)^(-2) η(20z) η(24z)^(-1) η(30z)^4 η(60z)^(-2) η(120z)`; see
[the local level table](../../TABLE.md#level-120).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z)^3 η(15z)^(-2) η(20z) η(24z)^(-1) η(30z)^4 η(60z)^(-2) η(120z)` at level 120. -/
abbrev cuspForm_120_eta_1m3_2p6_3p2_4m2_5p3_6m3_10m3_12p3_15m2_20p1_24m1_30p4_60m2_120p1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 3, 14 => -2, 19 => 1, 23 => -1, 29 => 4, 59 => -2, 119 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m3_2p6_3p2_4m2_5p3_6m3_10m3_12p3_15m2_20p1_24m1_30p4_60m2_120p1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m3_2p6_3p2_4m2_5p3_6m3_10m3_12p3_15m2_20p1_24m1_30p4_60m2_120p1 =
    [0, 0, 0, 0, 1, 3, 3, 2, 2, 0, -3, -2, 2, 2, 0, 1, -1, -8, -6, 2,
     -2, -2, 6, 4, -5, -2, 6, -2, -6, 2, 0, -14, -6, 2, -6, -4, 1, -2, -12, -2,
     5, 2, 0, 4, 2, 1, 6, 4, 4, -6, 0, 0, 4, 8, 9, 6, 6, 6, 6, 6,
     -1, 14, 0, 8, 11, 0, -6, 8, 8, -4, 0, 0, 2, -8, 18, 2, -8, -4, 0, -6,
     -4, -2, -12, -16, -6, 6, -18, -2, -14, -8, 3, 8, 0, -10, -18, -10, 3, -4, 12, -6] := by
  eta_coeff

end WeightTwoCusps
