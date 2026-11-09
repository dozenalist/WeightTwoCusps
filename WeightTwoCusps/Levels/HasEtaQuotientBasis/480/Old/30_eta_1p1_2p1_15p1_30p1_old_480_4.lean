module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».New.«30_eta_1p1_2p1_15p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(4z) η(8z) η(60z) η(120z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_30_eta_1p1_2p1_15p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(8z) η(60z) η(120z)` at level 480. -/
abbrev cuspForm_30_eta_1p1_2p1_15p1_30p1_old_480_4 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_30_eta_1p1_2p1_15p1_30p1 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_480_4_eq_eta :
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_480_4 =
      etaQuotientCuspForm 480 sparse![480; 3 => 1, 7 => 1, 59 => 1, 119 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_480_4_first_coeffs :
    first_coeffs 100 cuspForm_30_eta_1p1_2p1_15p1_30p1_old_480_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0,
     -1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
