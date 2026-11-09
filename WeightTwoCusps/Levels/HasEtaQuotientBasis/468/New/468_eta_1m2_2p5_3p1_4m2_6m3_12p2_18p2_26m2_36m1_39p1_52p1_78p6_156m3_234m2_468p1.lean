module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-3) η(12z)^2 η(18z)^2 η(26z)^(-2) η(36z)^(-1) η(39z) η(52z) η(78z)^6 η(156z)^(-3) η(234z)^(-2) η(468z)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-3) η(12z)^2 η(18z)^2 η(26z)^(-2) η(36z)^(-1) η(39z) η(52z) η(78z)^6 η(156z)^(-3) η(234z)^(-2) η(468z)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p5_3p1_4m2_6m3_12p2_18p2_26m2_36m1_39p1_52p1_78p6_156m3_234m2_468p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -3, 11 => 2, 17 => 2, 25 => -2, 35 => -1, 38 => 1, 51 => 1, 77 => 6, 155 => -3, 233 => -2, 467 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p5_3p1_4m2_6m3_12p2_18p2_26m2_36m1_39p1_52p1_78p6_156m3_234m2_468p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p5_3p1_4m2_6m3_12p2_18p2_26m2_36m1_39p1_52p1_78p6_156m3_234m2_468p1 =
    [0, 0, 1, 2, 0, -1, 0, 0, 2, 2, 0, -1, -2, 0, 2, 2, 0, -2, -2, 0,
     1, 0, 0, -2, -2, 0, 0, 0, 2, 2, -2, -2, 1, 2, 4, 2, -2, -2, -2, 0,
     4, 3, -6, -4, -1, 2, 2, -5, -2, -4, -1, 2, 0, -4, 0, 4, -2, 0, 2, 1,
     6, 4, -2, 0, -4, -1, 8, 6, -8, -4, -2, 3, 0, -10, 0, -4, -2, 0, 0, -8,
     -3, -2, -4, 5, 0, 2, 2, -4, -4, 3, 6, -2, 6, 4, -16, 4, 8, 6, -3, -14] := by
  eta_coeff

end WeightTwoCusps
