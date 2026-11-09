module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».New.«46_eta_1p1_2p1_23p1_46p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z) η(2z) η(23z) η(46z)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_46_eta_1p1_2p1_23p1_46p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(23z) η(46z)` at level 276. -/
abbrev cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_1 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_46_eta_1p1_2p1_23p1_46p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_1_eq_eta :
    cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_1 =
      etaQuotientCuspForm 276 sparse![276; 0 => 1, 1 => 1, 22 => 1, 45 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_1_first_coeffs :
    first_coeffs 100 cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_1 =
    [0, 0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2, -2, 0, 2, -1, 0,
     2, 0, 2, 0, 1, 0, -1, -1, 2, -1, 0, -3, -3, -2, 0, 4, -1, 2, 0, 3,
     -2, 1, 2, -2, 0, 0, 0, 1, -1, -4, 4, 4, -2, -2, -1, 0, 0, -2, 1, -4,
     6, 6, -3, -4, 2, -2, -4, 0, -4, 1, -4, 1, 3, 3, 0, 3, 2, 4, 3, 6,
     0, -4, 3, -6, 2, -4, 2, -3, -4, 2, -4, -4, -1, -3, 1, 4, -2, -2, 0, 2] := by
  eta_coeff

end WeightTwoCusps
