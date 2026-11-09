module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 88

The eta expression is `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^2 η(22z)^(-2) η(44z)^3 η(88z)^(-1)`; see
[the local level table](../../TABLE.md#level-88).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^2 η(22z)^(-2) η(44z)^3 η(88z)^(-1)` at level 88. -/
abbrev cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1 : gamma0CuspForms 88 :=
  etaQuotientCuspForm 88 sparse![88; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => 2, 21 => -2, 43 => 3, 87 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1 =
    [0, 1, 2, 1, 2, 1, -2, 2, 0, -2, 2, -1, -2, -4, -4, -7, -4, 6, -4, 0,
     2, -6, 2, 1, 0, 4, 8, 3, -4, 0, -2, 1, 8, -1, -4, 2, -4, -5, 0, 4,
     0, 0, 4, -10, 2, 6, -2, 8, 4, 5, -8, -2, 8, 2, 10, -1, 0, 8, 0, 3,
     -2, -4, 14, -4, -8, -4, -2, 7, -4, 1, -4, 3, 0, -4, 6, -4, 0, -2, -8, -6,
     -4, -7, -16, 6, 4, -10, -12, 0, 0, -9, -4, -16, -2, 1, 16, -16, -8, 9, -6, 2] := by
  eta_coeff

end WeightTwoCusps
