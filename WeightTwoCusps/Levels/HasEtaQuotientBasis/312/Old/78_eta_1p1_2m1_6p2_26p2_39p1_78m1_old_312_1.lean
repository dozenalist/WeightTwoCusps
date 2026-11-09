module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p1_2m1_6p2_26p2_39p1_78m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(z) η(2z)^(-1) η(6z)^2 η(26z)^2 η(39z) η(78z)^(-1)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(6z)^2 η(26z)^2 η(39z) η(78z)^(-1)` at level 312. -/
abbrev cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_312_1 : gamma0CuspForms 312 :=
  gamma0RescaleToLevel cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_312_1_eq_eta :
    cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_312_1 =
      etaQuotientCuspForm 312 sparse![312; 0 => 1, 1 => -1, 5 => 2, 25 => 2, 38 => 1, 77 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_312_1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1_old_312_1 =
    [0, 1, -1, 0, -1, 1, -1, -1, 1, 2, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0,
     -1, -1, 0, -2, 1, 1, 0, -3, 3, 0, 3, -2, 3, 2, -3, -4, 0, -1, 2, 0,
     0, 4, -1, 0, -2, 0, 2, 1, -2, 3, -2, -1, 0, 0, -1, -2, 0, 0, 0, 2,
     1, -2, 2, 0, -5, 0, 0, -2, -4, 0, 5, -1, 2, 4, 4, 5, 0, -6, 1, 6,
     -5, 2, -4, 2, -5, -3, 1, 4, -4, 6, -1, 0, 2, -6, 4, 0, -1, 2, -4, -2] := by
  eta_coeff

end WeightTwoCusps
