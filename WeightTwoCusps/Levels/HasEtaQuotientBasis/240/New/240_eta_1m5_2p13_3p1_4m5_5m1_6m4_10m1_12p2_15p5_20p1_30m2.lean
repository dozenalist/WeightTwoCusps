module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-5) η(2z)^13 η(3z) η(4z)^(-5) η(5z)^(-1) η(6z)^(-4) η(10z)^(-1) η(12z)^2 η(15z)^5 η(20z) η(30z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-5) η(2z)^13 η(3z) η(4z)^(-5) η(5z)^(-1) η(6z)^(-4) η(10z)^(-1) η(12z)^2 η(15z)^5 η(20z) η(30z)^(-2)` at level 240. -/
abbrev cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -5, 1 => 13, 2 => 1, 3 => -5, 4 => -1, 5 => -4, 9 => -1, 11 => 2, 14 => 5, 19 => 1, 29 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2 =
    [0, 1, 5, 7, -1, -5, 5, 8, 9, 9, -9, 0, 23, 14, 8, -7, -9, 6, 1, 20,
     1, -16, 8, -12, 9, 5, -22, -5, -20, 10, 7, -16, 9, -8, -2, -12, -25, 14, 12, -6,
     -9, -18, 0, 4, 0, -9, -28, 20, -9, -11, 13, -38, -2, -34, -7, 16, -36, 4, -14, -16,
     -23, -22, 0, 4, -9, -6, 8, 4, 42, -20, -16, 8, 9, 34, -6, 11, 4, 8, -22, 8,
     9, -27, 18, -12, 28, -14, -16, 30, 0, 18, -13, -24, -24, 40, 28, -28, 9, 10, 29, -8] := by
  eta_coeff

end WeightTwoCusps
