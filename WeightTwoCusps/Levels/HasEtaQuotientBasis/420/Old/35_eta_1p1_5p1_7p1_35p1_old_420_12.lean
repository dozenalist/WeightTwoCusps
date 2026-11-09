module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p1_5p1_7p1_35p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(12z) η(60z) η(84z) η(420z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(12z)` of `cuspForm_35_eta_1p1_5p1_7p1_35p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z) η(60z) η(84z) η(420z)` at level 420. -/
abbrev cuspForm_35_eta_1p1_5p1_7p1_35p1_old_420_12 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_35_eta_1p1_5p1_7p1_35p1 12

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_420_12_eq_eta :
    cuspForm_35_eta_1p1_5p1_7p1_35p1_old_420_12 =
      etaQuotientCuspForm 420 sparse![420; 11 => 1, 59 => 1, 83 => 1, 419 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_420_12_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p1_5p1_7p1_35p1_old_420_12 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
