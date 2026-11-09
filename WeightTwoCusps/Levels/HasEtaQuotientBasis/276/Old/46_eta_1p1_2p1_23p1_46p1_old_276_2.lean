module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».New.«46_eta_1p1_2p1_23p1_46p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(2z) η(4z) η(46z) η(92z)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_46_eta_1p1_2p1_23p1_46p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(46z) η(92z)` at level 276. -/
abbrev cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_2 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_46_eta_1p1_2p1_23p1_46p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_2_eq_eta :
    cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_2 =
      etaQuotientCuspForm 276 sparse![276; 1 => 1, 3 => 1, 45 => 1, 91 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_2_first_coeffs :
    first_coeffs 100 cuspForm_46_eta_1p1_2p1_23p1_46p1_old_276_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0, 0, 2, 0, 1, 0,
     0, 0, 0, 0, -2, 0, 1, 0, -2, 0, -2, 0, 0, 0, 2, 0, -1, 0, 0, 0,
     2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0, 2, 0, -1, 0,
     0, 0, -3, 0, -3, 0, -2, 0, 0, 0, 4, 0, -1, 0, 2, 0, 0, 0, 3, 0,
     -2, 0, 1, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -4, 0] := by
  eta_coeff

end WeightTwoCusps
