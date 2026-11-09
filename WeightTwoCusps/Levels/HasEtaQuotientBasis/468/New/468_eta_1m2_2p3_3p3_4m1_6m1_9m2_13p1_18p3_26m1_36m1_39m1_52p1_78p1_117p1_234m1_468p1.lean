module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-1) η(9z)^(-2) η(13z) η(18z)^3 η(26z)^(-1) η(36z)^(-1) η(39z)^(-1) η(52z) η(78z) η(117z) η(234z)^(-1) η(468z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-1) η(9z)^(-2) η(13z) η(18z)^3 η(26z)^(-1) η(36z)^(-1) η(39z)^(-1) η(52z) η(78z) η(117z) η(234z)^(-1) η(468z)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p3_3p3_4m1_6m1_9m2_13p1_18p3_26m1_36m1_39m1_52p1_78p1_117p1_234m1_468p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 8 => -2, 12 => 1, 17 => 3, 25 => -1, 35 => -1, 38 => -1, 51 => 1, 77 => 1, 116 => 1, 233 => -1, 467 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p3_3p3_4m1_6m1_9m2_13p1_18p3_26m1_36m1_39m1_52p1_78p1_117p1_234m1_468p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p3_3p3_4m1_6m1_9m2_13p1_18p3_26m1_36m1_39m1_52p1_78p1_117p1_234m1_468p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2,
     2, 1, 0, 2, 1, 0, 0, 2, 6, 2, 2, -1, 0, 1, -1, 2, -2, 3, 0, 1,
     -2, -6, 0, -2, 4, -2, -1, 2, 0, 0, -2, 0, -1, 2, 3, 6, 0, -2, 0, -2,
     0, -2, 2, 1, 4, 0, -2, -3, -6, 2, -3, 0, 0, -1, 2, -2, -4, 0, 0, -2,
     -6, -4, 4, 2, -3, -5, -2, -4, -2, -2, -2, -1, 2, 2, -2, -6, -4, 1, 2, 3] := by
  eta_coeff

end WeightTwoCusps
