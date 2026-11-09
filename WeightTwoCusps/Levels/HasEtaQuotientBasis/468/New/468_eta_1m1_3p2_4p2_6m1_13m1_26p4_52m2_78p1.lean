module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-1) η(3z)^2 η(4z)^2 η(6z)^(-1) η(13z)^(-1) η(26z)^4 η(52z)^(-2) η(78z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z)^2 η(6z)^(-1) η(13z)^(-1) η(26z)^4 η(52z)^(-2) η(78z)` at level 468. -/
abbrev cuspForm_468_eta_1m1_3p2_4p2_6m1_13m1_26p4_52m2_78p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -1, 2 => 2, 3 => 2, 5 => -1, 12 => -1, 25 => 4, 51 => -2, 77 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m1_3p2_4p2_6m1_13m1_26p4_52m2_78p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m1_3p2_4p2_6m1_13m1_26p4_52m2_78p1 =
    [0, 0, 0, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 0, 1, 2, 3, 3, 3, 1,
     3, 2, 2, 4, 3, 3, 0, 3, 3, 1, 2, -1, -2, 1, 0, 2, -5, 1, 3, 0,
     2, -2, -4, -2, -1, 3, -3, -1, 1, -3, -2, -2, 1, -3, -2, -1, -3, -1, 6, 0,
     3, -4, 5, 0, -6, 1, -2, 1, 3, -2, -4, -6, 1, 3, -2, -3, -2, 0, -2, 3,
     1, -5, -3, -6, -5, -4, -8, 0, -9, -6, 0, -1, -6, -1, -8, -4, -7, 0, -6, -10] := by
  eta_coeff

end WeightTwoCusps
