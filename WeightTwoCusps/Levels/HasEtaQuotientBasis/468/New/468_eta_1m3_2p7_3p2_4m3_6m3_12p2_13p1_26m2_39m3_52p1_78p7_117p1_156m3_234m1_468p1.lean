module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(13z) η(26z)^(-2) η(39z)^(-3) η(52z) η(78z)^7 η(117z) η(156z)^(-3) η(234z)^(-1) η(468z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(13z) η(26z)^(-2) η(39z)^(-3) η(52z) η(78z)^7 η(117z) η(156z)^(-3) η(234z)^(-1) η(468z)` at level 468. -/
abbrev cuspForm_468_eta_1m3_2p7_3p2_4m3_6m3_12p2_13p1_26m2_39m3_52p1_78p7_117p1_156m3_234m1_468p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 2, 12 => 1, 25 => -2, 38 => -3, 51 => 1, 77 => 7, 116 => 1, 155 => -3, 233 => -1, 467 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m3_2p7_3p2_4m3_6m3_12p2_13p1_26m2_39m3_52p1_78p7_117p1_156m3_234m1_468p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m3_2p7_3p2_4m3_6m3_12p2_13p1_26m2_39m3_52p1_78p7_117p1_156m3_234m1_468p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, -1, -1, 1,
     3, 1, 0, 2, -2, -2, 0, -1, -2, -5, 1, 3, -3, -4, -2, 0, 0, 1, 1, 0,
     -2, 3, 3, -4, -3, 0, 4, 1, 2, 0, -4, -1, 0, 5, 4, 4, 1, -2, 1, 1,
     1, -2, 3, -2, -6, 0, -4, -3, -11, 0, 9, -2, -3, -4, 4, -3, 1, 6, 0, -2,
     2, 6, -8, -7, -5, 3, 1, 0, 2, -7, -1, -1, 4, 0, 2, 6, 0, 6, -6, 0] := by
  eta_coeff

end WeightTwoCusps
