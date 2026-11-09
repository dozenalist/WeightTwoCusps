module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(6z) η(9z) η(18z)^(-1) η(90z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(6z) η(9z) η(18z)^(-1) η(90z)` at level 360. -/
abbrev cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1_old_360_1 : gamma0CuspForms 360 :=
  gamma0RescaleToLevel cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1_old_360_1_eq_eta :
    cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1_old_360_1 =
      etaQuotientCuspForm 360 sparse![360; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 5 => 1, 8 => 1, 17 => -1, 89 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1_old_360_1_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1_old_360_1 =
    [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, -1, 0, 0, -1, -2, -1, -2, -3, -2, -1,
     0, -2, 1, 0, -3, 0, 2, 0, 1, 0, 2, -2, -2, 2, 1, -1, 1, 3, -1, 2,
     0, 6, 2, 2, 4, 0, 0, 3, 4, -1, 0, 2, -3, -3, 1, 2, -2, -4, 2, 0,
     -1, 2, 4, -2, 3, -1, -6, -2, -5, 0, 0, -6, 2, -4, 0, 0, 3, 3, -4, -2,
     1, 1, -7, 3, -2, -1, -4, -2, -3, -6, -1, -1, 0, 4, -5, -1, 1, 0, 5, -2] := by
  eta_coeff

end WeightTwoCusps
