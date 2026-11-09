module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(8z) η(56z) η(64z) η(448z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(8z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z) η(56z) η(64z) η(448z)` at level 448. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_8 : gamma0CuspForms 448 :=
  gamma0Rescale cuspForm_56_eta_1p1_7p1_8p1_56p1 8

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_8_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_8 =
      etaQuotientCuspForm 448 sparse![448; 7 => 1, 55 => 1, 63 => 1, 447 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_8_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_8 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
