module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^4 η(4z)^(-1) η(6z)^(-3) η(9z)^(-1) η(12z) η(13z) η(26z)^(-3) η(36z) η(39z)^(-2) η(52z)^2 η(78z)^7 η(156z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^4 η(4z)^(-1) η(6z)^(-3) η(9z)^(-1) η(12z) η(13z) η(26z)^(-3) η(36z) η(39z)^(-2) η(52z)^2 η(78z)^7 η(156z)^(-3)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p3_3p4_4m1_6m3_9m1_12p1_13p1_26m3_36p1_39m2_52p2_78p7_156m3 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -3, 8 => -1, 11 => 1, 12 => 1, 25 => -3, 35 => 1, 38 => -2, 51 => 2, 77 => 7, 155 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p3_3p4_4m1_6m3_9m1_12p1_13p1_26m3_36p1_39m2_52p2_78p7_156m3_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p3_3p4_4m1_6m3_9m1_12p1_13p1_26m3_36p1_39m2_52p2_78p7_156m3 =
    [0, 0, 0, 1, 2, 2, 0, -2, 0, 1, 2, 0, -1, 0, -2, 1, -1, -2, -3, -2,
     2, 0, 1, 0, -1, -3, 0, 2, 1, 2, 3, 5, -2, -3, 0, 0, 1, -1, 2, 0,
     -2, 0, -3, -3, -4, 1, 1, 0, 3, 1, -2, -7, 0, 0, 2, 4, 4, 6, -3, 2,
     -1, -2, 2, 0, 4, 0, 0, -1, -8, -6, -5, -2, -2, -1, 4, -2, -5, -6, 0, 0,
     2, 5, 3, 4, 2, 9, -2, -6, -1, 2, 9, 0, 4, -4, -8, -4, -2, 5, -4, 1] := by
  eta_coeff

end WeightTwoCusps
