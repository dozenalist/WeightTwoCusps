module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(5z)^(-1) η(10z)^2 η(45z) η(75z)^3 η(150z)^(-1) η(225z)^(-1) η(450z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-1) η(10z)^2 η(45z) η(75z)^3 η(150z)^(-1) η(225z)^(-1) η(450z)` at level 450. -/
abbrev cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1_old_450_5 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1_old_450_5_eq_eta :
    cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1_old_450_5 =
      etaQuotientCuspForm 450 sparse![450; 4 => -1, 9 => 2, 44 => 1, 74 => 3, 149 => -1, 224 => -1, 449 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1_old_450_5_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1_old_450_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, -3, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
