module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-4) η(2z)^9 η(3z)^3 η(4z)^(-4) η(6z)^(-4) η(8z) η(9z)^(-1) η(12z) η(18z) η(24z)^2 η(36z) η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^9 η(3z)^3 η(4z)^(-4) η(6z)^(-4) η(8z) η(9z)^(-1) η(12z) η(18z) η(24z)^2 η(36z) η(72z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m4_2p9_3p3_4m4_6m4_8p1_9m1_12p1_18p1_24p2_36p1_72m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -4, 1 => 9, 2 => 3, 3 => -4, 5 => -4, 7 => 1, 8 => -1, 11 => 1, 17 => 1, 23 => 2, 35 => 1, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m4_2p9_3p3_4m4_6m4_8p1_9m1_12p1_18p1_24p2_36p1_72m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m4_2p9_3p3_4m4_6m4_8p1_9m1_12p1_18p1_24p2_36p1_72m1 =
    [0, 1, 4, 5, 1, -2, 1, 7, 6, 0, 1, 2, 2, 3, 6, 10, 0, -4, 1, 7,
     10, 0, 2, 0, 0, 2, -2, 5, 0, 2, -2, -7, 0, 0, -1, -4, -2, -2, -2, -10,
     0, 4, 0, -7, -20, 0, -4, 4, 0, -7, -10, -30, -2, 2, 1, -14, -24, 0, -3, -2,
     -4, -10, -14, -20, 0, 12, -4, -7, -10, 0, 0, -8, 0, -3, 0, -5, -4, 0, -2, -7,
     0, 0, 3, 6, 0, 5, -22, 10, 0, -8, -2, -14, 40, 0, 0, -4, 0, 9, -4, 20] := by
  eta_coeff

end WeightTwoCusps
