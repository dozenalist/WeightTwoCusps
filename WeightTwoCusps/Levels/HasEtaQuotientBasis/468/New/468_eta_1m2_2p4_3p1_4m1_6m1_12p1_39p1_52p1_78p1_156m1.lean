module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-1) η(12z) η(39z) η(52z) η(78z) η(156z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-1) η(12z) η(39z) η(52z) η(78z) η(156z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p4_3p1_4m1_6m1_12p1_39p1_52p1_78p1_156m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 11 => 1, 38 => 1, 51 => 1, 77 => 1, 155 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p4_3p1_4m1_6m1_12p1_39p1_52p1_78p1_156m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p4_3p1_4m1_6m1_12p1_39p1_52p1_78p1_156m1 =
    [0, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 0, 0, 1, 2, 2, 1, 1,
     1, 1, 2, 3, 1, 1, 0, 2, 1, 1, 2, 0, 2, 0, 2, 1, 0, 4, 2, 0,
     0, -1, 1, 0, 1, 1, -1, 1, -2, 0, 0, -1, 0, 0, -2, -2, -1, 0, 0, -3,
     -1, -3, -1, -1, -3, 0, -1, 2, -2, -2, 0, -3, 3, -3, -3, -2, -4, -1, 1, -3,
     -5, -4, -5, -3, -5, -4, -4, -2, -2, -5, -10, 0, 1, 0, -5, -5, -3, -3, 0, -4] := by
  eta_coeff

end WeightTwoCusps
