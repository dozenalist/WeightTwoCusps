module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«224».New.«224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(2z) η(4z)^(-1) η(8z) η(14z)^(-1) η(16z)^(-1) η(32z)^2 η(56z)^5 η(112z)^(-2)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z)^(-1) η(8z) η(14z)^(-1) η(16z)^(-1) η(32z)^2 η(56z)^5 η(112z)^(-2)` at level 448. -/
abbrev cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2_old_448_2 : gamma0CuspForms 448 :=
  gamma0Rescale cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2_old_448_2_eq_eta :
    cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2_old_448_2 =
      etaQuotientCuspForm 448 sparse![448; 1 => 1, 3 => -1, 7 => 1, 13 => -1, 15 => -1, 31 => 2, 55 => 5, 111 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2_old_448_2_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2_old_448_2 =
    [0, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0,
     0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 3, 0, -2, 0, -1, 0, -1, 0,
     0, 0, 0, 0, 2, 0, 3, 0, -2, 0, -3, 0, 0, 0, -2, 0, 0, 0, 2, 0,
     2, 0, 0, 0, -3, 0, 4, 0, -2, 0, 0, 0, 0, 0, 4, 0, -4, 0, -1, 0,
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -2, 0, 2, 0, -6, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
