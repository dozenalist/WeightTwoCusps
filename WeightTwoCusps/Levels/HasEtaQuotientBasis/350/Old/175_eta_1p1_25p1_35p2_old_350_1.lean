module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«175».New.«175_eta_1p1_25p1_35p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(z) η(25z) η(35z)^2`; see
[the local level table](../../TABLE.md#level-350).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_175_eta_1p1_25p1_35p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(25z) η(35z)^2` at level 350. -/
abbrev cuspForm_175_eta_1p1_25p1_35p2_old_350_1 : gamma0CuspForms 350 :=
  gamma0RescaleToLevel cuspForm_175_eta_1p1_25p1_35p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_175_eta_1p1_25p1_35p2_old_350_1_eq_eta :
    cuspForm_175_eta_1p1_25p1_35p2_old_350_1 =
      etaQuotientCuspForm 350 sparse![350; 0 => 1, 24 => 1, 34 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_175_eta_1p1_25p1_35p2_old_350_1_first_coeffs :
    first_coeffs 100 cuspForm_175_eta_1p1_25p1_35p2_old_350_1 =
    [0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 2, 1, 0, 0, -1, 0, -1, 0, 0, -3,
     2, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, -1,
     0, -2, 0, 0, 3, -4, -1, 0, 0, 4, 0, 2, 0, 0, 0, 1, -2, 0, 0, -1,
     -2, -2, 0, 0, 0, 0, 2, 0, 0, 4, -2, -2, 0, 0, 3, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
