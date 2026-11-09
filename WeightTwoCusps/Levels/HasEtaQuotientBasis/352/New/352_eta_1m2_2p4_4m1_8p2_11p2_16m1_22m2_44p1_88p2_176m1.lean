module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(8z)^2 η(11z)^2 η(16z)^(-1) η(22z)^(-2) η(44z) η(88z)^2 η(176z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(8z)^2 η(11z)^2 η(16z)^(-1) η(22z)^(-2) η(44z) η(88z)^2 η(176z)^(-1)` at level 352. -/
abbrev cuspForm_352_eta_1m2_2p4_4m1_8p2_11p2_16m1_22m2_44p1_88p2_176m1 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 0 => -2, 1 => 4, 3 => -1, 7 => 2, 10 => 2, 15 => -1, 21 => -2, 43 => 1, 87 => 2, 175 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_1m2_2p4_4m1_8p2_11p2_16m1_22m2_44p1_88p2_176m1_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_1m2_2p4_4m1_8p2_11p2_16m1_22m2_44p1_88p2_176m1 =
    [0, 1, 2, 1, 2, 3, 2, 4, 4, 2, 2, 5, 2, -2, 4, -1, 0, 4, -4, -2,
     2, 4, -2, 3, 4, -4, 8, -1, -4, 8, 2, -1, 0, 1, -4, 0, 4, -7, 0, 2,
     -12, -2, 4, -2, -2, -6, 2, -4, 0, 1, -8, 12, 0, -6, -10, -5, 8, -6, 0, -9,
     -6, 4, -14, -8, 0, 2, -2, -9, 4, -5, 4, 9, -8, 10, 6, -12, -8, 4, 8, -14,
     0, -7, -16, 10, -20, -8, 12, 12, -4, -13, -4, -8, 10, -1, -16, 10, 0, -23, -6, -10] := by
  eta_coeff

end WeightTwoCusps
