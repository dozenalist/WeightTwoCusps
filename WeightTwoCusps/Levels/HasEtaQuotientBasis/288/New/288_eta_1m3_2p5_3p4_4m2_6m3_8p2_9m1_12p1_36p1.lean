module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-2) η(6z)^(-3) η(8z)^2 η(9z)^(-1) η(12z) η(36z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-2) η(6z)^(-3) η(8z)^2 η(9z)^(-1) η(12z) η(36z)` at level 288. -/
abbrev cuspForm_288_eta_1m3_2p5_3p4_4m2_6m3_8p2_9m1_12p1_36p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 5, 2 => 4, 3 => -2, 5 => -3, 7 => 2, 8 => -1, 11 => 1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m3_2p5_3p4_4m2_6m3_8p2_9m1_12p1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m3_2p5_3p4_4m2_6m3_8p2_9m1_12p1_36p1 =
    [0, 0, 1, 3, 4, 3, 1, 3, 6, 6, 4, 0, 2, 3, 6, 6, 0, 3, 1, 3,
     -2, 0, 8, 0, 0, -3, 4, 3, 0, 3, -2, -3, 0, 0, -4, 0, -2, 0, -14, -6,
     0, -9, 0, -3, 4, -12, -16, 0, 0, 0, -7, -18, -8, -9, 1, -6, -24, 0, -12, 0,
     -4, 0, 10, -12, 0, -6, -4, -3, 2, 0, 0, 0, 0, -3, -18, -3, -16, 0, -2, -3,
     0, -18, 12, 0, 0, -9, -10, 6, 0, 3, -2, -6, -8, 0, 0, 0, 0, 9, 17, 12] := by
  eta_coeff

end WeightTwoCusps
