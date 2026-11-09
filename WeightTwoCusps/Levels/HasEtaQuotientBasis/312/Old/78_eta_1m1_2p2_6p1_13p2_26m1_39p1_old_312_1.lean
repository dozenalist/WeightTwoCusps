module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m1_2p2_6p1_13p2_26m1_39p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(z)^(-1) η(2z)^2 η(6z) η(13z)^2 η(26z)^(-1) η(39z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(6z) η(13z)^2 η(26z)^(-1) η(39z)` at level 312. -/
abbrev cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1_old_312_1 : gamma0CuspForms 312 :=
  gamma0RescaleToLevel cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1_old_312_1_eq_eta :
    cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1_old_312_1 =
      etaQuotientCuspForm 312 sparse![312; 0 => -1, 1 => 2, 5 => 1, 12 => 2, 25 => -1, 38 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1_old_312_1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1_old_312_1 =
    [0, 0, 1, 1, 0, 1, 0, 0, 0, -1, 0, -1, 1, 0, -2, -3, -2, 0, -3, 0,
     -1, 0, 2, 0, 1, -2, 0, 4, 2, -2, 1, 2, 1, 3, 0, 0, -1, 2, 2, 0,
     0, -1, 3, -2, -1, -1, -2, 3, 1, 2, 1, -5, 0, 2, 6, 4, 0, 6, -2, 1,
     -5, -4, 0, -4, 4, 1, -8, -6, 4, -2, -6, -1, -4, -2, -2, 0, -2, -2, -2, 0,
     -1, -13, 6, -1, 2, 2, -4, 6, -2, 1, 7, 0, 0, 0, 0, -2, 0, 6, 1, 13] := by
  eta_coeff

end WeightTwoCusps
