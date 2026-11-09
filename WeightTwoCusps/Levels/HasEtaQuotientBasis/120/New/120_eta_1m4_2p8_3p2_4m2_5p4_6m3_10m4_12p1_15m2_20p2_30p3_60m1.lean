module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^2 η(4z)^(-2) η(5z)^4 η(6z)^(-3) η(10z)^(-4) η(12z) η(15z)^(-2) η(20z)^2 η(30z)^3 η(60z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^2 η(4z)^(-2) η(5z)^4 η(6z)^(-3) η(10z)^(-4) η(12z) η(15z)^(-2) η(20z)^2 η(30z)^3 η(60z)^(-1)` at level 120. -/
abbrev cuspForm_120_eta_1m4_2p8_3p2_4m2_5p4_6m3_10m4_12p1_15m2_20p2_30p3_60m1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -4, 1 => 8, 2 => 2, 3 => -2, 4 => 4, 5 => -3, 9 => -4, 11 => 1, 14 => -2, 19 => 2, 29 => 3, 59 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m4_2p8_3p2_4m2_5p4_6m3_10m4_12p1_15m2_20p2_30p3_60m1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m4_2p8_3p2_4m2_5p4_6m3_10m4_12p1_15m2_20p2_30p3_60m1 =
    [0, 1, 4, 6, 6, 7, 4, -4, -6, -3, -4, -2, 6, 4, -4, 0, 6, -4, -8, 4,
     -6, -18, 0, 10, -6, -5, 8, -12, -24, -8, -4, -20, -6, 18, 0, -4, 6, 0, -16, -6,
     6, -6, -4, -2, 0, 3, 12, 10, 6, 9, 4, 6, 12, 12, 16, 22, 24, 12, 0, 2,
     -6, 10, 8, 12, 6, -8, 0, 14, 36, 12, 4, 0, -6, -18, 8, 12, -24, -16, 8, 0,
     -6, 9, 0, -22, -24, 8, -28, -6, 0, 6, 8, 8, 0, -36, -12, -20, -6, -14, 12, -18] := by
  eta_coeff

end WeightTwoCusps
