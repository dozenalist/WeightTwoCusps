module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(5z)^(-2) η(10z)^2 η(15z)^2 η(20z)^3 η(40z)^(-1) η(60z)^(-1) η(120z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-2) η(10z)^2 η(15z)^2 η(20z)^3 η(40z)^(-1) η(60z)^(-1) η(120z)` at level 480. -/
abbrev cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_480_5 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_480_5_eq_eta :
    cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_480_5 =
      etaQuotientCuspForm 480 sparse![480; 4 => -2, 9 => 2, 14 => 2, 19 => 3, 39 => -1, 59 => -1, 119 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_480_5_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_480_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 0,
     4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
