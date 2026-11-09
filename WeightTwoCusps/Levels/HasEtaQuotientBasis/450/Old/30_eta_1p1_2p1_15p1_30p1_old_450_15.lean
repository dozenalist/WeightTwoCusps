module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».New.«30_eta_1p1_2p1_15p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(15z) η(30z) η(225z) η(450z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(15z)` of `cuspForm_30_eta_1p1_2p1_15p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(15z) η(30z) η(225z) η(450z)` at level 450. -/
abbrev cuspForm_30_eta_1p1_2p1_15p1_30p1_old_450_15 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_30_eta_1p1_2p1_15p1_30p1 15

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_450_15_eq_eta :
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_450_15 =
      etaQuotientCuspForm 450 sparse![450; 14 => 1, 29 => 1, 224 => 1, 449 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_450_15_first_coeffs :
    first_coeffs 100 cuspForm_30_eta_1p1_2p1_15p1_30p1_old_450_15 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
