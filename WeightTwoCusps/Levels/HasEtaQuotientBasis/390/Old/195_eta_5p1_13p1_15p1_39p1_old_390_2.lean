module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«195».New.«195_eta_5p1_13p1_15p1_39p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(10z) η(26z) η(30z) η(78z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_195_eta_5p1_13p1_15p1_39p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(10z) η(26z) η(30z) η(78z)` at level 390. -/
abbrev cuspForm_195_eta_5p1_13p1_15p1_39p1_old_390_2 : gamma0CuspForms 390 :=
  gamma0Rescale cuspForm_195_eta_5p1_13p1_15p1_39p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_195_eta_5p1_13p1_15p1_39p1_old_390_2_eq_eta :
    cuspForm_195_eta_5p1_13p1_15p1_39p1_old_390_2 =
      etaQuotientCuspForm 390 sparse![390; 9 => 1, 25 => 1, 29 => 1, 77 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_5p1_13p1_15p1_39p1_old_390_2_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_5p1_13p1_15p1_39p1_old_390_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -1, 0,
     0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 2, 0, 1, 0,
     0, 0, -2, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
