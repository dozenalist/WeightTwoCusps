module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-5) η(2z)^11 η(3z)^5 η(4z)^(-4) η(5z) η(6z)^(-4) η(10z)^(-2) η(12z) η(15z)^(-1) η(20z) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-5) η(2z)^11 η(3z)^5 η(4z)^(-4) η(5z) η(6z)^(-4) η(10z)^(-2) η(12z) η(15z)^(-1) η(20z) η(30z)` at level 120. -/
abbrev cuspForm_120_eta_1m5_2p11_3p5_4m4_5p1_6m4_10m2_12p1_15m1_20p1_30p1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -5, 1 => 11, 2 => 5, 3 => -4, 4 => 1, 5 => -4, 9 => -2, 11 => 1, 14 => -1, 19 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m5_2p11_3p5_4m4_5p1_6m4_10m2_12p1_15m1_20p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m5_2p11_3p5_4m4_5p1_6m4_10m2_12p1_15m1_20p1_30p1 =
    [0, 1, 5, 9, 5, -7, -15, -10, -5, -9, -5, 4, 5, -2, 0, 17, 5, 2, 25, 16,
     -5, -30, 0, 22, -5, 29, 10, -21, -20, -14, 15, -32, -5, 36, -10, -10, 5, 6, -20, -18,
     5, -6, -40, -26, 0, -17, 20, 10, 5, 33, 5, 18, 10, 18, 5, -28, 20, 24, 10, -16,
     -5, -2, 0, 30, 5, 14, 0, 26, 30, 18, 0, -12, -5, -30, 10, -19, -20, -40, -30, 12,
     -5, 21, 10, -34, -20, -14, -40, -6, 0, -6, -25, 20, 0, -48, -20, 48, -5, -38, 5, -36] := by
  eta_coeff

end WeightTwoCusps
