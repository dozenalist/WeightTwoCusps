module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(6z) η(42z) η(48z) η(336z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(42z) η(48z) η(336z)` at level 336. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_336_6 : gamma0CuspForms 336 :=
  gamma0Rescale cuspForm_56_eta_1p1_7p1_8p1_56p1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_336_6_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_336_6 =
      etaQuotientCuspForm 336 sparse![336; 5 => 1, 41 => 1, 47 => 1, 335 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_336_6_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_336_6 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
