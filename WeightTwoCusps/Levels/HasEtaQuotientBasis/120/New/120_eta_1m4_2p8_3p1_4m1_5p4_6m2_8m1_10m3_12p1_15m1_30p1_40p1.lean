module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-4) η(2z)^8 η(3z) η(4z)^(-1) η(5z)^4 η(6z)^(-2) η(8z)^(-1) η(10z)^(-3) η(12z) η(15z)^(-1) η(30z) η(40z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z) η(4z)^(-1) η(5z)^4 η(6z)^(-2) η(8z)^(-1) η(10z)^(-3) η(12z) η(15z)^(-1) η(30z) η(40z)` at level 120. -/
abbrev cuspForm_120_eta_1m4_2p8_3p1_4m1_5p4_6m2_8m1_10m3_12p1_15m1_30p1_40p1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -4, 1 => 8, 2 => 1, 3 => -1, 4 => 4, 5 => -2, 7 => -1, 9 => -3, 11 => 1, 14 => -1, 29 => 1, 39 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m4_2p8_3p1_4m1_5p4_6m2_8m1_10m3_12p1_15m1_30p1_40p1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m4_2p8_3p1_4m1_5p4_6m2_8m1_10m3_12p1_15m1_30p1_40p1 =
    [0, 0, 1, 4, 6, 7, 10, 6, -3, -2, -4, -10, 3, 10, -4, -1, 0, -20, -17, -2,
     -3, -4, 6, 8, -6, -6, 8, -2, -18, 2, -7, -26, -3, 6, 0, -4, 6, -10, -16, 2,
     6, 6, 8, 16, -6, 11, 6, 8, 9, -18, 1, -12, 6, 12, 16, 14, 18, 2, 0, 22,
     -6, 34, 8, -4, 12, 0, -6, 12, 30, 6, 4, 0, -3, -16, 20, 10, -12, 4, 14, -10,
     -9, -2, -18, -20, -18, 10, -22, 6, -6, 0, 14, 8, 0, -34, -18, -30, -6, 4, 21, -6] := by
  eta_coeff

end WeightTwoCusps
