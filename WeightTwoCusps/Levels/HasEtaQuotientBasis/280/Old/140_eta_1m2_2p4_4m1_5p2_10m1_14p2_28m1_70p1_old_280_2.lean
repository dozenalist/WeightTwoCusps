module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«140».New.«140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(10z)^2 η(20z)^(-1) η(28z)^2 η(56z)^(-1) η(140z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(10z)^2 η(20z)^(-1) η(28z)^2 η(56z)^(-1) η(140z)` at level 280. -/
abbrev cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_280_2 : gamma0CuspForms 280 :=
  gamma0Rescale cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_280_2_eq_eta :
    cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_280_2 =
      etaQuotientCuspForm 280 sparse![280; 1 => -2, 3 => 4, 7 => -1, 9 => 2, 19 => -1, 27 => 2, 55 => -1, 139 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_280_2_first_coeffs :
    first_coeffs 100 cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_280_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, -3, 0, -4, 0, -2, 0,
     -4, 0, -6, 0, 0, 0, -2, 0, -4, 0, 2, 0, -2, 0, -5, 0, 0, 0, 0, 0,
     -6, 0, 2, 0, 0, 0, -1, 0, 2, 0, -4, 0, -2, 0, 2, 0, 0, 0, -4, 0,
     4, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4, 0, 8, 0] := by
  eta_coeff

end WeightTwoCusps
