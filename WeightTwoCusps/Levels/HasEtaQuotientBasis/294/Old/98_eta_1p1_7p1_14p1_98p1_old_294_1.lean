module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«98».New.«98_eta_1p1_7p1_14p1_98p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z) η(7z) η(14z) η(98z)`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_98_eta_1p1_7p1_14p1_98p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z) η(14z) η(98z)` at level 294. -/
abbrev cuspForm_98_eta_1p1_7p1_14p1_98p1_old_294_1 : gamma0CuspForms 294 :=
  gamma0RescaleToLevel cuspForm_98_eta_1p1_7p1_14p1_98p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_98_eta_1p1_7p1_14p1_98p1_old_294_1_eq_eta :
    cuspForm_98_eta_1p1_7p1_14p1_98p1_old_294_1 =
      etaQuotientCuspForm 294 sparse![294; 0 => 1, 6 => 1, 13 => 1, 97 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_1p1_7p1_14p1_98p1_old_294_1_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_1p1_7p1_14p1_98p1_old_294_1 =
    [0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 1, 1, 0, 0, -2, 0, -3,
     1, 2, 0, 0, -1, 0, -1, 1, -1, 0, 0, 4, 0, 1, 1, 0, 0, 0, -2, 0,
     1, -5, -2, 0, 0, -1, 0, 4, 0, -1, 0, 0, 1, 0, 3, -2, 1, 0, 0, 1,
     0, -1, 2, -1, 0, 0, 1, 0, -2, 2, 0, 0, 0, -1, 0, -4, -3, 0, 0, 0,
     1, 0, -2, 5, 2, 0, 0, -4, 0, -1, -1, 4, 0, 0, -2, 0, -1, 6, 1, 0] := by
  eta_coeff

end WeightTwoCusps
