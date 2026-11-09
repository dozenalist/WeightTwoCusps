module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«99».New.«99_eta_1p1_9p1_11p1_99p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(2z) η(18z) η(22z) η(198z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_99_eta_1p1_9p1_11p1_99p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(18z) η(22z) η(198z)` at level 396. -/
abbrev cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_2 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_99_eta_1p1_9p1_11p1_99p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_2_eq_eta :
    cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_2 =
      etaQuotientCuspForm 396 sparse![396; 1 => 1, 17 => 1, 21 => 1, 197 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_2_first_coeffs :
    first_coeffs 100 cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0,
     -1, 0, -2, 0, 0, 0, -2, 0, 1, 0, 2, 0, 0, 0, -1, 0, 1, 0, 2, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -2, 0, -1, 0, 2, 0,
     -3, 0, 2, 0, 0, 0, 1, 0, 0, 0, -1, 0, -2, 0, 0, 0, -1, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
