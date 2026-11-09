module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^4 η(4z)^(-2) η(6z)^(-4) η(9z)^(-2) η(12z) η(13z) η(18z)^3 η(26z)^(-1) η(36z)^(-1) η(39z)^(-2) η(78z)^3 η(117z)^2 η(234z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^4 η(4z)^(-2) η(6z)^(-4) η(9z)^(-2) η(12z) η(13z) η(18z)^3 η(26z)^(-1) η(36z)^(-1) η(39z)^(-2) η(78z)^3 η(117z)^2 η(234z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m3_2p6_3p4_4m2_6m4_9m2_12p1_13p1_18p3_26m1_36m1_39m2_78p3_117p2_234m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 6, 2 => 4, 3 => -2, 5 => -4, 8 => -2, 11 => 1, 12 => 1, 17 => 3, 25 => -1, 35 => -1, 38 => -2, 77 => 3, 116 => 2, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m3_2p6_3p4_4m2_6m4_9m2_12p1_13p1_18p3_26m1_36m1_39m2_78p3_117p2_234m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m3_2p6_3p4_4m2_6m4_9m2_12p1_13p1_18p3_26m1_36m1_39m2_78p3_117p2_234m1 =
    [0, 0, 0, 0, 0, 0, 1, 3, 3, 0, -4, -3, 2, 3, 2, -2, -2, 0, -1, 1,
     -5, -4, -2, 0, 3, -4, -1, -6, -1, 0, 0, 5, -3, 6, -1, 4, 2, -4, 4, 0,
     8, 4, 6, 2, -2, -4, 0, 5, -2, 0, -3, 4, 1, 2, -5, -8, -4, 0, 11, -8,
     -2, -4, 0, 6, -8, -1, -8, 3, 4, 4, 4, -4, -3, -10, 6, 4, 3, 4, -1, 2,
     2, 6, -2, -6, -6, 10, 8, 0, 6, -2, 2, -7, 0, 4, -2, 0, -1, 4, -7, -2] := by
  eta_coeff

end WeightTwoCusps
