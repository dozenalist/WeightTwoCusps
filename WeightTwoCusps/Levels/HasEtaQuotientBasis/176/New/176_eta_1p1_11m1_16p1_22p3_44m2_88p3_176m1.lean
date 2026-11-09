module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 176

The eta expression is `η(z) η(11z)^(-1) η(16z) η(22z)^3 η(44z)^(-2) η(88z)^3 η(176z)^(-1)`; see
[the local level table](../../TABLE.md#level-176).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(11z)^(-1) η(16z) η(22z)^3 η(44z)^(-2) η(88z)^3 η(176z)^(-1)` at level 176. -/
abbrev cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1 : gamma0CuspForms 176 :=
  etaQuotientCuspForm 176 sparse![176; 0 => 1, 10 => -1, 15 => 1, 21 => 3, 43 => -2, 87 => 3, 175 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 1, -2, -1, 0, -1, 0,
     1, 2, 0, 0, -1, 0, -1, 1, 0, 0, -2, 2, 0, 0, 1, -2, 2, 1, -1, 0,
     1, 0, -1, -2, 0, 0, 0, 2, 1, -2, 1, -2, 0, -2, 2, 0, -2, 0, 0, -1,
     2, 0, 0, 0, 2, 4, 0, 1, -2, -1, 1, 2, -2, 0, -1, 2, -4, 0, 1, 0,
     -1, 2, -1, 2, -2, -2, -2, -4, 1, 0, 2, -2, 2, 1, 2, 0, 0, -4, 0, 1] := by
  eta_coeff

end WeightTwoCusps
