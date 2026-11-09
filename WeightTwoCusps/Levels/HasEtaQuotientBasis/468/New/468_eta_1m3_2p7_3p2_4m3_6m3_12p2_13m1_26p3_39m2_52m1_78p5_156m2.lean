module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(13z)^(-1) η(26z)^3 η(39z)^(-2) η(52z)^(-1) η(78z)^5 η(156z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(13z)^(-1) η(26z)^3 η(39z)^(-2) η(52z)^(-1) η(78z)^5 η(156z)^(-2)` at level 468. -/
abbrev cuspForm_468_eta_1m3_2p7_3p2_4m3_6m3_12p2_13m1_26p3_39m2_52m1_78p5_156m2 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 2, 12 => -1, 25 => 3, 38 => -2, 51 => -1, 77 => 5, 155 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m3_2p7_3p2_4m3_6m3_12p2_13m1_26p3_39m2_52m1_78p5_156m2_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m3_2p7_3p2_4m3_6m3_12p2_13m1_26p3_39m2_52m1_78p5_156m2 =
    [0, 1, 3, 2, -1, -1, 1, 3, 1, 0, 2, -2, -2, 0, 1, 4, -1, -1, 1, -1,
     2, 0, 0, 4, -3, -3, 0, -4, -1, -7, -2, 3, -6, -4, -3, 2, 0, -2, 1, 0,
     0, 7, 8, -6, -7, 0, 6, 2, 2, 1, -8, -6, 0, 7, 7, 2, 1, 2, 3, 3,
     0, 0, 3, -4, -7, 0, -8, -7, -19, -4, 14, -9, -7, -8, 6, -4, -1, 12, -1, -4,
     3, 12, -12, -13, -4, 2, 2, 4, -2, -9, -2, -1, 14, -2, 4, 14, 1, 16, -8, 0] := by
  eta_coeff

end WeightTwoCusps
