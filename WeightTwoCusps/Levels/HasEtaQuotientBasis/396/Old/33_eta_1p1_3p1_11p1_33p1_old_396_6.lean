module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«33».New.«33_eta_1p1_3p1_11p1_33p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(6z) η(18z) η(66z) η(198z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_33_eta_1p1_3p1_11p1_33p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(18z) η(66z) η(198z)` at level 396. -/
abbrev cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_6 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_33_eta_1p1_3p1_11p1_33p1 6 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_6_eq_eta :
    cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_6 =
      etaQuotientCuspForm 396 sparse![396; 5 => 1, 17 => 1, 65 => 1, 197 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_6_first_coeffs :
    first_coeffs 100 cuspForm_33_eta_1p1_3p1_11p1_33p1_old_396_6 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
