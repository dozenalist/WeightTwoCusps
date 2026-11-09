module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».New.«30_eta_1p1_2p1_15p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(2z) η(4z) η(30z) η(60z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_30_eta_1p1_2p1_15p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(30z) η(60z)` at level 360. -/
abbrev cuspForm_30_eta_1p1_2p1_15p1_30p1_old_360_2 : gamma0CuspForms 360 :=
  gamma0RescaleToLevel cuspForm_30_eta_1p1_2p1_15p1_30p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_360_2_eq_eta :
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_360_2 =
      etaQuotientCuspForm 360 sparse![360; 1 => 1, 3 => 1, 29 => 1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_360_2_first_coeffs :
    first_coeffs 100 cuspForm_30_eta_1p1_2p1_15p1_30p1_old_360_2 =
    [0, 0, 0, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0,
     0, 0, -2, 0, 1, 0, -2, 0, -2, 0, 0, 0, 2, 0, -2, 0, 1, 0, 4, 0,
     -1, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 2, 0, 2, 0,
     -1, 0, -4, 0, -3, 0, 2, 0, 4, 0, -2, 0, -2, 0, -6, 0, 0, 0, 0, 0,
     0, 0, 8, 0, -2, 0, 4, 0, 6, 0, 1, 0, 0, 0, 4, 0, -3, 0, -8, 0] := by
  eta_coeff

end WeightTwoCusps
