module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-3) η(9z)^(-1) η(12z) η(13z) η(18z)^3 η(26z)^(-2) η(36z)^(-1) η(39z)^(-3) η(52z) η(78z)^7 η(117z) η(156z)^(-2) η(234z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-3) η(9z)^(-1) η(12z) η(13z) η(18z)^3 η(26z)^(-2) η(36z)^(-1) η(39z)^(-3) η(52z) η(78z)^7 η(117z) η(156z)^(-2) η(234z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p4_3p2_4m1_6m3_9m1_12p1_13p1_18p3_26m2_36m1_39m3_52p1_78p7_117p1_156m2_234m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -3, 8 => -1, 11 => 1, 12 => 1, 17 => 3, 25 => -2, 35 => -1, 38 => -3, 51 => 1, 77 => 7, 116 => 1, 155 => -2, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p4_3p2_4m1_6m3_9m1_12p1_13p1_18p3_26m2_36m1_39m3_52p1_78p7_117p1_156m2_234m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p4_3p2_4m1_6m3_9m1_12p1_13p1_18p3_26m2_36m1_39m3_52p1_78p7_117p1_156m2_234m1 =
    [0, 1, 2, 1, 0, -1, 0, 2, 2, 2, -1, -1, 1, 2, 2, -1, -1, -2, 1, 1,
     -1, -1, -4, 0, 0, 0, 0, -2, 1, 0, 0, 0, 1, 2, 0, 2, 0, 2, 2, 0,
     3, 1, 2, 1, 0, -2, 1, 2, 1, -1, -3, 2, 0, 2, 0, -2, -4, 0, 4, -1,
     -1, -5, 0, 2, -1, 0, -4, 0, 0, 0, 2, -2, -1, -3, 0, 1, 2, 2, -1, -1,
     -4, 1, 0, 0, -1, -2, 0, -2, 1, 0, -1, -7, 0, 2, -2, 2, -2, 1, -4, -2] := by
  eta_coeff

end WeightTwoCusps
