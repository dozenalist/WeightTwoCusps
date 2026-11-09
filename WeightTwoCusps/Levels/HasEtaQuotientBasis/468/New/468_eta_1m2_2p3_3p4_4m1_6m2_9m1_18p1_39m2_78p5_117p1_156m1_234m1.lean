module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^4 η(4z)^(-1) η(6z)^(-2) η(9z)^(-1) η(18z) η(39z)^(-2) η(78z)^5 η(117z) η(156z)^(-1) η(234z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^4 η(4z)^(-1) η(6z)^(-2) η(9z)^(-1) η(18z) η(39z)^(-2) η(78z)^5 η(117z) η(156z)^(-1) η(234z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p3_3p4_4m1_6m2_9m1_18p1_39m2_78p5_117p1_156m1_234m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -2, 8 => -1, 17 => 1, 38 => -2, 77 => 5, 116 => 1, 155 => -1, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p3_3p4_4m1_6m2_9m1_18p1_39m2_78p5_117p1_156m1_234m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p3_3p4_4m1_6m2_9m1_18p1_39m2_78p5_117p1_156m1_234m1 =
    [0, 0, 1, 2, 2, 0, -2, 0, 0, 0, -2, -1, 2, -2, 0, -2, 0, 0, -2, 2,
     -3, -2, -2, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, -2, 0, 4, 0, 2, 0,
     0, 2, 4, 6, 0, -6, 0, 1, -2, -2, -2, 8, 0, 0, -4, -2, 0, -4, 4, -6,
     -2, -6, 0, 6, 0, -1, -4, 6, 4, 0, -2, 0, -2, -6, 2, 6, 0, 4, 0, -2,
     0, 2, 4, -4, -2, 0, 2, -4, 4, 0, 6, 8, -2, 0, -4, 0, -2, 0, 0, 4] := by
  eta_coeff

end WeightTwoCusps
