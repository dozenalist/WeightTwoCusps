module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«99».New.«99_eta_1p1_9p1_11p1_99p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(4z) η(36z) η(44z) η(396z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_99_eta_1p1_9p1_11p1_99p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(36z) η(44z) η(396z)` at level 396. -/
abbrev cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_4 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_99_eta_1p1_9p1_11p1_99p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_4_eq_eta :
    cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_4 =
      etaQuotientCuspForm 396 sparse![396; 3 => 1, 35 => 1, 43 => 1, 395 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_4_first_coeffs :
    first_coeffs 100 cuspForm_99_eta_1p1_9p1_11p1_99p1_old_396_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
