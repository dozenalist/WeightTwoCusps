module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_1p1_3m1_6p2_38p1_57p2_114m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z) η(3z)^(-1) η(6z)^2 η(38z) η(57z)^2 η(114z)^(-1)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z)^(-1) η(6z)^2 η(38z) η(57z)^2 η(114z)^(-1)` at level 228. -/
abbrev cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1_old_228_1 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1_old_228_1_eq_eta :
    cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1_old_228_1 =
      etaQuotientCuspForm 228 sparse![228; 0 => 1, 2 => -1, 5 => 2, 37 => 1, 56 => 2, 113 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1_old_228_1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1_old_228_1 =
    [0, 0, 1, -1, -1, 1, -1, 0, 0, 1, 1, 1, 0, -1, -1, 0, 1, -2, 1, 0,
     0, -1, -1, -1, 1, 1, -1, 2, 1, 0, 0, 1, 0, 0, -1, -1, 0, 1, 0, 1,
     -2, 1, 1, -1, 0, -1, 0, -1, -2, -2, 0, 0, 2, 1, 1, 1, 0, 0, 1, -1,
     2, 3, -2, 1, 1, -1, -4, -4, -1, 0, 3, 3, 0, 0, 4, -4, 0, -1, 2, 2,
     2, -4, -2, 4, -4, -3, 1, -1, -4, 3, -1, 3, -1, 4, -3, 0, -3, 5, 0, -1] := by
  eta_coeff

end WeightTwoCusps
