module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(5z) η(35z) η(40z) η(280z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z) η(35z) η(40z) η(280z)` at level 280. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_5 : gamma0CuspForms 280 :=
  gamma0Rescale cuspForm_56_eta_1p1_7p1_8p1_56p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_5_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_5 =
      etaQuotientCuspForm 280 sparse![280; 4 => 1, 34 => 1, 39 => 1, 279 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_5_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_280_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
