module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«168».New.«168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(4z)^(-1) η(8z)^3 η(12z)^2 η(16z)^(-1) η(24z)^(-2) η(28z) η(48z) η(56z) η(112z)^(-1) η(336z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z)^3 η(12z)^2 η(16z)^(-1) η(24z)^(-2) η(28z) η(48z) η(56z) η(112z)^(-1) η(336z)` at level 336. -/
abbrev cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_2 : gamma0CuspForms 336 :=
  gamma0Rescale cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_2_eq_eta :
    cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_2 =
      etaQuotientCuspForm 336 sparse![336; 3 => -1, 7 => 3, 11 => 2, 15 => -1, 23 => -2, 27 => 1, 47 => 1, 55 => 1, 111 => -1, 335 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_2_first_coeffs :
    first_coeffs 100 cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_old_336_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0,
     0, 0, -1, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 1, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 3, 0,
     0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -3, 0, 0, 0, -2, 0, 0, 0, 4, 0,
     0, 0, 3, 0, 0, 0, 4, 0, 0, 0, -3, 0, 0, 0, -6, 0, 0, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
