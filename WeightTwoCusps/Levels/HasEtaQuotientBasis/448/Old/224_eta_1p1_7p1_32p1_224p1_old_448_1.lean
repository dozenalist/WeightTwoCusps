module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«224».New.«224_eta_1p1_7p1_32p1_224p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(z) η(7z) η(32z) η(224z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_224_eta_1p1_7p1_32p1_224p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z) η(32z) η(224z)` at level 448. -/
abbrev cuspForm_224_eta_1p1_7p1_32p1_224p1_old_448_1 : gamma0CuspForms 448 :=
  gamma0RescaleToLevel cuspForm_224_eta_1p1_7p1_32p1_224p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_224_eta_1p1_7p1_32p1_224p1_old_448_1_eq_eta :
    cuspForm_224_eta_1p1_7p1_32p1_224p1_old_448_1 =
      etaQuotientCuspForm 448 sparse![448; 0 => 1, 6 => 1, 31 => 1, 223 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_1p1_7p1_32p1_224p1_old_448_1_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_1p1_7p1_32p1_224p1_old_448_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 1,
     1, 0, 0, -2, 0, -2, 0, 1, 0, 0, 0, 0, -1, 2, 0, 0, 0, 2, 0, 0,
     0, 0, 0, -1, 0, 1, 0, -2, -2, 0, 0, -2, -1, 2, 0, 2, 0, 2, 0, -1,
     2, -2, 0, 0, 1, 0, 0, 1, 2, -3, 0, 0, 0, 0, 0, -3, 1, 1, 0, 2,
     0, -2, 0, 0, -1, -2, 0, 2, 0, 2, 0, -1, -2, 2, 0, 0, 2, -2, 0, -1] := by
  eta_coeff

end WeightTwoCusps
