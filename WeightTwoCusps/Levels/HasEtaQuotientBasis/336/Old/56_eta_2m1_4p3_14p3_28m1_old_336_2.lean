module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_2m1_4p3_14p3_28m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(4z)^(-1) η(8z)^3 η(28z)^3 η(56z)^(-1)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_56_eta_2m1_4p3_14p3_28m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z)^3 η(28z)^3 η(56z)^(-1)` at level 336. -/
abbrev cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_2 : gamma0CuspForms 336 :=
  gamma0RescaleToLevel cuspForm_56_eta_2m1_4p3_14p3_28m1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_2_eq_eta :
    cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_2 =
      etaQuotientCuspForm 336 sparse![336; 3 => -1, 7 => 3, 27 => 3, 55 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_2_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_2m1_4p3_14p3_28m1_old_336_2 =
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0,
     0, 0, -2, 0, 0, 0, 1, 0, 0, 0, -4, 0, 0, 0, -4, 0, 0, 0, 3, 0,
     0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, -2, 0, 0, 0, 4, 0,
     0, 0, 6, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, -4, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -5, 0, 0, 0, -6, 0, 0, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
