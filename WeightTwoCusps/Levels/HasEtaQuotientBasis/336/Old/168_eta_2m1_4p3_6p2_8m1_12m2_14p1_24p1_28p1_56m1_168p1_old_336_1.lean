module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«168».New.«168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(2z)^(-1) η(4z)^3 η(6z)^2 η(8z)^(-1) η(12z)^(-2) η(14z) η(24z) η(28z) η(56z)^(-1) η(168z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^3 η(6z)^2 η(8z)^(-1) η(12z)^(-2) η(14z) η(24z) η(28z) η(56z)^(-1) η(168z)` at level 336. -/
abbrev cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_1 : gamma0CuspForms 336 :=
  gamma0RescaleToLevel cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_1_eq_eta :
    cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_1 =
      etaQuotientCuspForm 336 sparse![336; 1 => -1, 3 => 3, 5 => 2, 7 => -1, 11 => -2, 13 => 1, 23 => 1, 27 => 1, 55 => -1, 167 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_1_first_coeffs :
    first_coeffs 100 cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -2, 0, -2, 0, 1, 0, 1,
     0, -1, 0, 0, 0, -1, 0, 2, 0, 3, 0, 1, 0, 1, 0, -3, 0, -2, 0, 4,
     0, 3, 0, 4, 0, -3, 0, -6, 0, 1, 0, -3, 0, 3, 0, -2, 0, -7, 0, -3,
     0, -2, 0, 3, 0, 1, 0, -2, 0, 2, 0, -1, 0, 0, 0, 9, 0, 3, 0, 5,
     0, -5, 0, -1, 0, 4, 0, 3, 0, 3, 0, -3, 0, 1, 0, -1, 0, -2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
