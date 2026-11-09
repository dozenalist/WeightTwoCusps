module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-5) η(2z)^11 η(3z) η(4z)^(-4) η(5z)^5 η(6z)^(-2) η(10z)^(-4) η(12z) η(15z)^(-1) η(20z) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-5) η(2z)^11 η(3z) η(4z)^(-4) η(5z)^5 η(6z)^(-2) η(10z)^(-4) η(12z) η(15z)^(-1) η(20z) η(30z)` at level 120. -/
abbrev cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -5, 1 => 11, 2 => 1, 3 => -4, 4 => 5, 5 => -2, 9 => -4, 11 => 1, 14 => -1, 19 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1 =
    [0, 1, 5, 9, 9, 13, 17, 2, -9, 3, -5, -20, 9, 22, -8, -3, 9, -22, -31, -8,
     -9, -18, 0, 10, -9, -11, 10, -9, -36, -14, -17, -32, -9, 12, 6, 2, 9, -18, -20, 6,
     9, -6, 16, 34, 0, 15, 12, 22, 9, -15, 5, -6, 18, 18, 29, 28, 36, 0, -6, 32,
     -9, 46, 16, -6, 9, -2, 0, 14, 54, 6, 8, 12, -9, -30, 10, 21, -36, 8, 34, -12,
     -9, -3, -6, -22, -36, 2, -32, -6, 0, 42, 31, -4, 0, -48, -12, -56, -9, 10, 21, -12] := by
  eta_coeff

end WeightTwoCusps
