module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-4) η(9z)^(-1) η(12z) η(13z)^2 η(18z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z) η(234z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-4) η(9z)^(-1) η(12z) η(13z)^2 η(18z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z) η(234z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m4_2p8_3p4_4m3_6m4_9m1_12p1_13p2_18p1_26m1_39m2_78p3_117p1_234m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -4, 8 => -1, 11 => 1, 12 => 2, 17 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 1, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m4_2p8_3p4_4m3_6m4_9m1_12p1_13p2_18p1_26m1_39m2_78p3_117p1_234m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m4_2p8_3p4_4m3_6m4_9m1_12p1_13p2_18p1_26m1_39m2_78p3_117p1_234m1 =
    [0, 0, 1, 4, 6, 4, 0, 0, 6, 8, 6, 5, 4, 6, 4, 6, 4, -6, 0, 6,
     11, 0, -10, 0, -2, 4, 0, 4, 2, -8, 4, -4, 4, -6, -6, 6, -4, 8, -4, 0,
     0, -10, 0, 10, 14, -4, -8, 3, 16, 2, -2, 4, 0, 2, 6, 10, -18, -12, 4, 22,
     10, -22, 0, -10, 4, 1, -8, 6, -8, 4, -6, -4, -10, -14, -2, 0, 4, -20, -2, -6,
     -22, -16, 0, 20, -16, -16, -10, 0, -8, -8, 4, -24, 0, 0, 12, -8, -24, 0, -8, 10] := by
  eta_coeff

end WeightTwoCusps
