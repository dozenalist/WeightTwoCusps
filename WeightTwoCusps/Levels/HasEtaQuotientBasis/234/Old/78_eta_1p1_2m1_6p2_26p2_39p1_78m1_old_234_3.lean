module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p1_2m1_6p2_26p2_39p1_78m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(3z) η(6z)^(-1) η(18z)^2 η(78z)^2 η(117z) η(234z)^(-1)`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(6z)^(-1) η(18z)^2 η(78z)^2 η(117z) η(234z)^(-1)` at level 234. -/
abbrev cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_234_3 : gamma0CuspForms 234 :=
  gamma0Rescale cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_234_3_eq_eta :
    cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_234_3 =
      etaQuotientCuspForm 234 sparse![234; 2 => 1, 5 => -1, 17 => 2, 77 => 2, 116 => 1, 233 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_234_3_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_234_3 =
    [0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0,
     0, -1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
     0, -3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, -2, 0, 0, 3, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
