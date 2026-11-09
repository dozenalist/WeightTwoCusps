module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_2m1_4p3_14p3_28m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(6z)^(-1) η(12z)^3 η(42z)^3 η(84z)^(-1)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_56_eta_2m1_4p3_14p3_28m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z)^3 η(42z)^3 η(84z)^(-1)` at level 336. -/
abbrev cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_3 : gamma0CuspForms 336 :=
  gamma0RescaleToLevel cuspForm_56_eta_2m1_4p3_14p3_28m1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_3_eq_eta :
    cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_3 =
      etaQuotientCuspForm 336 sparse![336; 5 => -1, 11 => 3, 41 => 3, 83 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_3_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_3 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1,
     0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 3, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0,
     0, -2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
