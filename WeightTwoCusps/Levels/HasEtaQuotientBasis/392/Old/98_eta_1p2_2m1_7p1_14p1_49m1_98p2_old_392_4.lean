module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«98».New.«98_eta_1p2_2m1_7p1_14p1_49m1_98p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(4z)^2 η(8z)^(-1) η(28z) η(56z) η(196z)^(-1) η(392z)^2`; see
[the local level table](../../TABLE.md#level-392).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(8z)^(-1) η(28z) η(56z) η(196z)^(-1) η(392z)^2` at level 392. -/
abbrev cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_392_4 : gamma0CuspForms 392 :=
  gamma0Rescale cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_392_4_eq_eta :
    cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_392_4 =
      etaQuotientCuspForm 392 sparse![392; 3 => 2, 7 => -1, 27 => 1, 55 => 1, 195 => -1, 391 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_392_4_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_392_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
