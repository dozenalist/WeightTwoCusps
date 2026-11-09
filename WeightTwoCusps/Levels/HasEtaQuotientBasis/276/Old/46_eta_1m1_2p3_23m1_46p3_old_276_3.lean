module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».New.«46_eta_1m1_2p3_23m1_46p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(3z)^(-1) η(6z)^3 η(69z)^(-1) η(138z)^3`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_46_eta_1m1_2p3_23m1_46p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^3 η(69z)^(-1) η(138z)^3` at level 276. -/
abbrev cuspForm_46_eta_1m1_2p3_23m1_46p3_old_276_3 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_46_eta_1m1_2p3_23m1_46p3 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_46_eta_1m1_2p3_23m1_46p3_old_276_3_eq_eta :
    cuspForm_46_eta_1m1_2p3_23m1_46p3_old_276_3 =
      etaQuotientCuspForm 276 sparse![276; 2 => -1, 5 => 3, 68 => -1, 137 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_46_eta_1m1_2p3_23m1_46p3_old_276_3_first_coeffs :
    first_coeffs 100 cuspForm_46_eta_1m1_2p3_23m1_46p3_old_276_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0,
     0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -2, 0, 0, 1, 0, 0, -1, 0, 0, -1,
     0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
     2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 1, 0,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
