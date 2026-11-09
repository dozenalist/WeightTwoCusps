module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«140».New.«140_eta_1p1_7p1_20p1_140p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z) η(7z) η(20z) η(140z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_140_eta_1p1_7p1_20p1_140p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z) η(20z) η(140z)` at level 420. -/
abbrev cuspForm_140_eta_1p1_7p1_20p1_140p1_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_140_eta_1p1_7p1_20p1_140p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_140_eta_1p1_7p1_20p1_140p1_old_420_1_eq_eta :
    cuspForm_140_eta_1p1_7p1_20p1_140p1_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => 1, 6 => 1, 19 => 1, 139 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_140_eta_1p1_7p1_20p1_140p1_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_140_eta_1p1_7p1_20p1_140p1_old_420_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 1, 1, 0, 0, -2,
     0, -2, 0, 1, 0, 0, 0, -1, 0, 3, 0, 0, -1, 2, 0, -1, -1, 0, 0, 2,
     -1, 2, 0, -3, -1, 0, 0, -2, 2, 1, 0, 0, -1, -2, 0, -1, 1, -2, 0, 2,
     1, 4, 0, 2, 3, -1, 0, 1, 1, -4, 0, -2, -1, -2, 0, 0, -2, 0, 0, 0,
     1, -2, 0, 1, -1, 1, 0, 1, 0, -2, 0, 2, 2, 2, 0, 0, -4, 4, 0, 2] := by
  eta_coeff

end WeightTwoCusps
