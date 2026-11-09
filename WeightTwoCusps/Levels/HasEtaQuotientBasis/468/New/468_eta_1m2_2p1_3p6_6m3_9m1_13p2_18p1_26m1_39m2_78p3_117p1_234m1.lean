module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-3) η(9z)^(-1) η(13z)^2 η(18z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z) η(234z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-3) η(9z)^(-1) η(13z)^2 η(18z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z) η(234z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p1_3p6_6m3_9m1_13p2_18p1_26m1_39m2_78p3_117p1_234m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 1, 2 => 6, 5 => -3, 8 => -1, 12 => 2, 17 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 1, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p1_3p6_6m3_9m1_13p2_18p1_26m1_39m2_78p3_117p1_234m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p1_3p6_6m3_9m1_13p2_18p1_26m1_39m2_78p3_117p1_234m1 =
    [0, 0, 1, 2, 4, 2, 2, 0, 4, 4, 4, 3, 2, 4, 4, 4, 4, -4, 2, 0,
     7, -2, -4, 0, 0, 4, 0, 0, 0, -6, 4, -4, 2, -2, 0, 4, -4, 4, -2, 0,
     0, -6, 0, 4, 8, 2, -8, 3, 6, 4, -2, 0, 0, 4, 6, 8, -12, -4, 0, 14,
     0, -8, 0, -4, 4, 1, -8, 0, -8, 4, -8, -4, -4, -4, -2, -2, 0, -12, -2, -4,
     -14, -6, 0, 12, -6, -12, -4, -4, -4, -6, -2, -16, 2, 4, 4, -4, -14, 0, -6, -2] := by
  eta_coeff

end WeightTwoCusps
