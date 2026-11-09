module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».New.«70_eta_1p1_5p2_10m1_14p1_35m1_70p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(4z) η(20z)^2 η(40z)^(-1) η(56z) η(140z)^(-1) η(280z)^2`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(20z)^2 η(40z)^(-1) η(56z) η(140z)^(-1) η(280z)^2` at level 280. -/
abbrev cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_280_4 : gamma0CuspForms 280 :=
  gamma0Rescale cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_280_4_eq_eta :
    cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_280_4 =
      etaQuotientCuspForm 280 sparse![280; 3 => 1, 19 => 2, 39 => -1, 55 => 1, 139 => -1, 279 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_280_4_first_coeffs :
    first_coeffs 100 cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_280_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
