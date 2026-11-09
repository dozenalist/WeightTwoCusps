module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».New.«30_eta_1p1_2p1_15p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 90

The eta expression is `η(3z) η(6z) η(45z) η(90z)`; see
[the local level table](../../TABLE.md#level-90).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_30_eta_1p1_2p1_15p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(6z) η(45z) η(90z)` at level 90. -/
abbrev cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_3 : gamma0CuspForms 90 :=
  gamma0Rescale cuspForm_30_eta_1p1_2p1_15p1_30p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_3_eq_eta :
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_3 =
      etaQuotientCuspForm 90 sparse![90; 2 => 1, 5 => 1, 44 => 1, 89 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_3_first_coeffs :
    first_coeffs 100 cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_3 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0,
     0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, -2,
     0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 1, 0, 0, 4, 0, 0,
     -1, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 2, 0, 0, 2, 0, 0, -1, 0, 0, -4, 0, 0, -3, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
