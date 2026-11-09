module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(13z) η(26z)^(-3) η(39z)^(-2) η(52z)^3 η(78z)^5 η(156z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(13z) η(26z)^(-3) η(39z)^(-2) η(52z)^3 η(78z)^5 η(156z)^(-2)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p4_3p1_4m1_13p1_26m3_39m2_52p3_78p5_156m2 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 12 => 1, 25 => -3, 38 => -2, 51 => 3, 77 => 5, 155 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p4_3p1_4m1_13p1_26m3_39m2_52p3_78p5_156m2_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p4_3p1_4m1_13p1_26m3_39m2_52p3_78p5_156m2 =
    [0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 1, -1, 1, 0, 0, 2, -2, -2, -3, 0,
     0, -3, -1, -2, 0, -2, 0, -1, -3, 2, 3, 4, -1, 0, 4, 3, 1, -2, 1, -1,
     3, 5, -5, -4, -4, 3, 0, -5, -1, -2, 1, -3, 1, -5, -2, 2, 2, 4, -6, 0,
     3, 4, -2, -3, 1, -2, 4, 1, -3, -2, -4, 3, -2, -2, 0, 1, 1, -7, 1, -4,
     3, 1, 1, 7, -5, 2, 3, 2, -3, 1, 7, -1, 3, -2, -3, -2, -6, 2, -3, -3] := by
  eta_coeff

end WeightTwoCusps
