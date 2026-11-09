module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(6z) η(12z)^(-1) η(13z)^(-1) η(26z)^4 η(52z)^(-1) η(78z)^(-1) η(156z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(6z) η(12z)^(-1) η(13z)^(-1) η(26z)^4 η(52z)^(-1) η(78z)^(-1) η(156z)` at level 468. -/
abbrev cuspForm_468_eta_1m1_3p2_4p1_6p1_12m1_13m1_26p4_52m1_78m1_156p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 11 => -1, 12 => -1, 25 => 4, 51 => -1, 77 => -1, 155 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m1_3p2_4p1_6p1_12m1_13m1_26p4_52m1_78m1_156p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m1_3p2_4p1_6p1_12m1_13m1_26p4_52m1_78m1_156p1 =
    [0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 2, 1, 2, 0, 2, 1, 2, 2, 1, 3,
     5, 3, 4, 2, 3, 2, 1, 4, 1, 4, 4, 2, 0, 0, 2, 0, -2, 2, -4, 1,
     0, 1, 0, -2, 5, -3, -7, -1, -4, 2, 0, 0, -2, -4, 4, -2, -4, -4, 2, -3,
     -3, -4, 0, -3, 6, -1, -4, -4, -4, 2, -6, -3, -1, -7, -4, -4, -8, -2, 0, -2,
     -7, -10, -4, -1, -5, -2, -2, -2, 2, -1, -2, -2, 2, 2, -2, -4, -11, 7, 2, 6] := by
  eta_coeff

end WeightTwoCusps
