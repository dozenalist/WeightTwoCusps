module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«105».New.«105_eta_1p1_3p1_35p1_105p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(4z) η(12z) η(140z) η(420z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_105_eta_1p1_3p1_35p1_105p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(12z) η(140z) η(420z)` at level 420. -/
abbrev cuspForm_105_eta_1p1_3p1_35p1_105p1_old_420_4 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_105_eta_1p1_3p1_35p1_105p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_105_eta_1p1_3p1_35p1_105p1_old_420_4_eq_eta :
    cuspForm_105_eta_1p1_3p1_35p1_105p1_old_420_4 =
      etaQuotientCuspForm 420 sparse![420; 3 => 1, 11 => 1, 139 => 1, 419 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_105_eta_1p1_3p1_35p1_105p1_old_420_4_first_coeffs :
    first_coeffs 100 cuspForm_105_eta_1p1_3p1_35p1_105p1_old_420_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     1, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
