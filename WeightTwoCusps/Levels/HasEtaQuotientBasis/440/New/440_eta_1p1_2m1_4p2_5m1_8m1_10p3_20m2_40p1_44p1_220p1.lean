module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(z) η(2z)^(-1) η(4z)^2 η(5z)^(-1) η(8z)^(-1) η(10z)^3 η(20z)^(-2) η(40z) η(44z) η(220z)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(4z)^2 η(5z)^(-1) η(8z)^(-1) η(10z)^3 η(20z)^(-2) η(40z) η(44z) η(220z)` at level 440. -/
abbrev cuspForm_440_eta_1p1_2m1_4p2_5m1_8m1_10p3_20m2_40p1_44p1_220p1 : gamma0CuspForms 440 :=
  etaQuotientCuspForm 440 sparse![440; 0 => 1, 1 => -1, 3 => 2, 4 => -1, 7 => -1, 9 => 3, 19 => -2, 39 => 1, 43 => 1, 219 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_440_eta_1p1_2m1_4p2_5m1_8m1_10p3_20m2_40p1_44p1_220p1_first_coeffs :
    first_coeffs 100 cuspForm_440_eta_1p1_2m1_4p2_5m1_8m1_10p3_20m2_40p1_44p1_220p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, -1, 2, 0, 1,
     -1, -1, 0, 2, 0, 2, 0, -1, 0, -3, 0, -1, 0, 0, 0, -2, 1, 0, 0, 2,
     2, 2, 0, 1, 0, 0, 0, -3, 0, 0, 0, 1, -2, -4, 0, 0, 0, 3, 0, 3,
     0, -3, 0, -1, 1, 5, 0, -4, 0, -4, 0, 3, -2, 3, 0, 0, 0, 0, 0, 2,
     -1, 2, 0, 1, -2, -2, 0, -1, 0, 0, 0, 2, 1, -2, 0, -5, 2, 6, 0, 0] := by
  eta_coeff

end WeightTwoCusps
