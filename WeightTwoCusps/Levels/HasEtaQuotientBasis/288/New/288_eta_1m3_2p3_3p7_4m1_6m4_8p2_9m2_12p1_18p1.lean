module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^3 η(3z)^7 η(4z)^(-1) η(6z)^(-4) η(8z)^2 η(9z)^(-2) η(12z) η(18z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^3 η(3z)^7 η(4z)^(-1) η(6z)^(-4) η(8z)^2 η(9z)^(-2) η(12z) η(18z)` at level 288. -/
abbrev cuspForm_288_eta_1m3_2p3_3p7_4m1_6m4_8p2_9m2_12p1_18p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 3, 2 => 7, 3 => -1, 5 => -4, 7 => 2, 8 => -2, 11 => 1, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m3_2p3_3p7_4m1_6m4_8p2_9m2_12p1_18p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m3_2p3_3p7_4m1_6m4_8p2_9m2_12p1_18p1 =
    [0, 1, 3, 6, 6, 4, 3, 6, 12, 9, 6, 0, 6, 12, 12, 12, 0, 8, 3, 6,
     0, 0, 12, 0, 0, -7, 6, 6, 0, -4, -6, -6, 0, 0, -6, 0, -6, -2, -24, -12,
     0, -8, 0, -6, 0, -18, -24, 0, 0, -7, -15, -36, -12, -4, 3, -12, -48, 0, -18, 0,
     -12, -10, 12, -24, 0, -24, -12, -6, 0, 0, 0, 0, 0, -12, -30, -6, -24, 0, -6, -6,
     0, -27, 18, 0, 0, -22, -24, 12, 0, 16, -6, -12, 0, 0, 0, 0, 0, 36, 27, 24] := by
  eta_coeff

end WeightTwoCusps
