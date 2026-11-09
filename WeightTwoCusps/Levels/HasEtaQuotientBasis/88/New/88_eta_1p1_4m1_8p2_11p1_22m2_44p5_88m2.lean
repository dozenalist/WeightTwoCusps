module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 88

The eta expression is `η(z) η(4z)^(-1) η(8z)^2 η(11z) η(22z)^(-2) η(44z)^5 η(88z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z) η(4z)^(-1) η(8z)^2 η(11z) η(22z)^(-2) η(44z)^5 η(88z)^(-2)` at level 88. -/
abbrev cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2 : gamma0CuspForms 88 :=
  etaQuotientCuspForm 88 sparse![88; 0 => 1, 3 => -1, 7 => 2, 10 => 1, 21 => -2, 43 => 5, 87 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2 =
    [0, 1, -1, -1, 0, 1, 0, -1, 1, 0, 1, 0, 0, 1, 0, -1, -2, -1, 2, -1,
     0, -1, 0, 1, -1, 0, 0, 3, 0, -2, 2, 1, 2, 0, -2, 3, 0, -1, -4, 1,
     1, -3, -2, -4, 0, -4, 2, 6, 2, 1, 0, 3, 0, 0, 0, 0, -2, -1, 0, 3,
     0, 6, -6, -2, 0, -3, 1, -1, 0, 1, 4, -3, -2, 5, -1, -4, 0, -1, 4, -8,
     -2, -1, 4, -2, 0, 3, 8, 6, 1, 9, -2, -10, 0, 1, -4, -5, -2, 1, 3, -2] := by
  eta_coeff

end WeightTwoCusps
