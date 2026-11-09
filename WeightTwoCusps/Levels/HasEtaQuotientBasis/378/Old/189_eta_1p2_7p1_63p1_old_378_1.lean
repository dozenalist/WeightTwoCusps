module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«189».New.«189_eta_1p2_7p1_63p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z)^2 η(7z) η(63z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_189_eta_1p2_7p1_63p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(7z) η(63z)` at level 378. -/
abbrev cuspForm_189_eta_1p2_7p1_63p1_old_378_1 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_189_eta_1p2_7p1_63p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_189_eta_1p2_7p1_63p1_old_378_1_eq_eta :
    cuspForm_189_eta_1p2_7p1_63p1_old_378_1 =
      etaQuotientCuspForm 378 sparse![378; 0 => 2, 6 => 1, 62 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_1p2_7p1_63p1_old_378_1_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_1p2_7p1_63p1_old_378_1 =
    [0, 0, 0, 1, -2, -1, 2, 1, 2, -2, -1, 0, -1, -1, -1, -2, 4, 2, 2, 5,
     -3, -1, -4, -2, -3, 4, -2, -2, 0, 4, 2, -5, 4, 1, 3, 0, 2, -2, 1, -2,
     0, -1, 1, -6, -2, 4, -6, -2, -1, 0, 2, 6, 6, -4, 2, 7, -1, 4, -4, 2,
     -4, -7, -1, 2, 0, 0, -4, 2, 2, -3, 1, 0, -6, -2, 2, -1, 6, 1, 2, 0,
     -3, -2, 1, 6, 1, 6, 6, 1, 0, -1, -4, -3, -8, 0, 9, -6, -2, -11, 0, -8] := by
  eta_coeff

end WeightTwoCusps
