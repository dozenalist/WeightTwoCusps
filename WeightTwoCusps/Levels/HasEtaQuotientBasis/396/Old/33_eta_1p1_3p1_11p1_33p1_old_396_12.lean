module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«33».New.«33_eta_1p1_3p1_11p1_33p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(12z) η(36z) η(132z) η(396z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(12z)` of `cuspForm_33_eta_1p1_3p1_11p1_33p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z) η(36z) η(132z) η(396z)` at level 396. -/
abbrev cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_12 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_33_eta_1p1_3p1_11p1_33p1 12

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_12_eq_eta :
    cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_12 =
      etaQuotientCuspForm 396 sparse![396; 11 => 1, 35 => 1, 131 => 1, 395 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_12_first_coeffs :
    first_coeffs 100 cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_12 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
