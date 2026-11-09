module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«195».New.«195_eta_1p1_3p1_65p1_195p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z) η(3z) η(65z) η(195z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_195_eta_1p1_3p1_65p1_195p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z) η(65z) η(195z)` at level 390. -/
abbrev cuspForm_195_eta_1p1_3p1_65p1_195p1_old_390_1 : gamma0CuspForms 390 :=
  gamma0RescaleToLevel cuspForm_195_eta_1p1_3p1_65p1_195p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_195_eta_1p1_3p1_65p1_195p1_old_390_1_eq_eta :
    cuspForm_195_eta_1p1_3p1_65p1_195p1_old_390_1 =
      etaQuotientCuspForm 390 sparse![390; 0 => 1, 2 => 1, 64 => 1, 194 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1p1_3p1_65p1_195p1_old_390_1_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1p1_3p1_65p1_195p1_old_390_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, 1, 2, -1, 2, 0,
     0, -1, -1, -1, -1, 0, 1, -1, -1, 2, 0, 1, 2, 1, -1, 0, -1, 2, -1, 0,
     -1, -1, 0, -1, -1, 0, -1, -2, 2, 2, 0, -1, 1, 0, 1, 0, -1, 2, 2, 1,
     0, -2, 2, -1, 0, -1, -1, -1, 1, -1, 0, 0, -1, -1, -1, 0, -1, 3, -1, 0,
     -1, -3, 2, 0, 2, 0, 1, 3, 0, 2, -1, 0, 0, 1, 0, 0, 0, -2, -2, 2] := by
  eta_coeff

end WeightTwoCusps
