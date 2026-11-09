module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«33».New.«33_eta_1p1_3p1_11p1_33p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z) η(3z) η(11z) η(33z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_33_eta_1p1_3p1_11p1_33p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z) η(11z) η(33z)` at level 396. -/
abbrev cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_33_eta_1p1_3p1_11p1_33p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_1_eq_eta :
    cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => 1, 2 => 1, 10 => 1, 32 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_1 =
    [0, 0, 1, -1, -1, -1, 1, 2, -1, 2, 0, 0, -1, -2, 0, 0, 1, 0, -3, 0,
     0, 0, 1, 3, 1, 1, 2, 0, 0, -2, 2, -5, -1, -1, -2, -2, 3, 1, 0, -2,
     2, 2, -4, 2, -1, 1, 2, 0, 3, 4, -3, 2, -2, 4, -1, -1, -4, 0, -2, -3,
     -2, -2, 2, -2, 5, 0, 1, 1, 2, -2, -4, 1, -1, -6, 4, 3, 0, 2, 6, 2,
     2, -5, -6, 6, 4, 2, -4, 2, -1, -7, -4, 0, -2, -2, 8, 0, -7, 3, 1, 2] := by
  eta_coeff

end WeightTwoCusps
