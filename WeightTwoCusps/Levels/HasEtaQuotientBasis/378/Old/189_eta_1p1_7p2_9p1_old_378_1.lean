module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«189».New.«189_eta_1p1_7p2_9p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z) η(7z)^2 η(9z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_189_eta_1p1_7p2_9p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z)^2 η(9z)` at level 378. -/
abbrev cuspForm_189_eta_1p1_7p2_9p1_old_378_1 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_189_eta_1p1_7p2_9p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_189_eta_1p1_7p2_9p1_old_378_1_eq_eta :
    cuspForm_189_eta_1p1_7p2_9p1_old_378_1 =
      etaQuotientCuspForm 378 sparse![378; 0 => 1, 6 => 2, 8 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_1p1_7p2_9p1_old_378_1_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_1p1_7p2_9p1_old_378_1 =
    [0, 1, -1, -1, 0, 0, 1, 0, -1, 2, 1, 1, 1, -3, 0, -4, 0, 2, -2, -3,
     2, 1, 4, 1, 0, 0, 0, 2, -2, 2, -2, 1, -1, 5, -3, -1, -2, -5, -6, 2,
     0, -2, 2, 5, 3, -4, 6, -2, 1, 1, 0, 0, 2, -4, -2, 11, 2, -4, 4, 2,
     -2, -3, -4, -2, -8, -2, 4, -6, 2, -3, -1, -3, 6, 4, 5, 1, -10, 0, 4, -1,
     8, 2, -1, 0, -1, 3, -2, -1, 0, 6, 4, -1, 7, 0, -9, 1, -7, 1, -1, 8] := by
  eta_coeff

end WeightTwoCusps
