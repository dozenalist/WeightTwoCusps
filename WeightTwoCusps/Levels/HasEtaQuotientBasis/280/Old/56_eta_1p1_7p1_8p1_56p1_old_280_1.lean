module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(z) η(7z) η(8z) η(56z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z) η(8z) η(56z)` at level 280. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_1 : gamma0CuspForms 280 :=
  gamma0RescaleToLevel cuspForm_56_eta_1p1_7p1_8p1_56p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_1_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_1 =
      etaQuotientCuspForm 280 sparse![280; 0 => 1, 6 => 1, 7 => 1, 55 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_1_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 2, 1, 0, -2, -1, -2, 0, -1,
     0, 1, 0, 2, -2, 4, 0, -2, -1, 2, 0, 2, 1, 0, 0, -1, -1, -2, 0, -2,
     0, -2, 0, 0, 0, -1, 0, 2, 2, 0, 0, 2, 4, -4, 0, 0, 1, 0, 0, 3,
     0, -1, 0, 0, -1, 0, 0, -2, -6, 4, 0, 0, 1, -4, 0, 3, -2, 0, 0, -4,
     0, 0, 0, 3, 2, 2, 0, -2, 0, 4, 0, 1, 0, 0, 0, 2, -2, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
