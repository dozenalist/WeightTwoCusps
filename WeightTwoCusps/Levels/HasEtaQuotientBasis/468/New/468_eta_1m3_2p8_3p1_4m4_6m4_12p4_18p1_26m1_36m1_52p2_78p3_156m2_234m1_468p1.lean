module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-4) η(6z)^(-4) η(12z)^4 η(18z) η(26z)^(-1) η(36z)^(-1) η(52z)^2 η(78z)^3 η(156z)^(-2) η(234z)^(-1) η(468z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-4) η(6z)^(-4) η(12z)^4 η(18z) η(26z)^(-1) η(36z)^(-1) η(52z)^2 η(78z)^3 η(156z)^(-2) η(234z)^(-1) η(468z)` at level 468. -/
abbrev cuspForm_468_eta_1m3_2p8_3p1_4m4_6m4_12p4_18p1_26m1_36m1_52p2_78p3_156m2_234m1_468p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 8, 2 => 1, 3 => -4, 5 => -4, 11 => 4, 17 => 1, 25 => -1, 35 => -1, 51 => 2, 77 => 3, 155 => -2, 233 => -1, 467 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m3_2p8_3p1_4m4_6m4_12p4_18p1_26m1_36m1_52p2_78p3_156m2_234m1_468p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m3_2p8_3p1_4m4_6m4_12p4_18p1_26m1_36m1_52p2_78p3_156m2_234m1_468p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, -3, 0, 3, 2, 3, 1, 0,
     0, -3, 2, 6, 0, -3, 0, 3, 1, -3, 1, 3, 0, 0, -1, 3, 1, -3, 1, 0,
     0, 0, 2, 6, 1, -6, 0, 3, 2, 6, 0, 0, 1, -3, 0, 3, 1, 0, 1, 0,
     -1, -3, 0, 0, -3, 0, -1, 0, 0, -6, -2, -3, 1, 3, 0, 6, -3, -6, 1, 3,
     -1, 3, 1, 0, -1, -9, 0, 0, -1, -9, -6, 12, -1, -12, -6, -6, -4, 0, 1, 6] := by
  eta_coeff

end WeightTwoCusps
