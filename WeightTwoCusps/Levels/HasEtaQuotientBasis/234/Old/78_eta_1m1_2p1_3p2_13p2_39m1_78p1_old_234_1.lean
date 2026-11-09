module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m1_2p1_3p2_13p2_39m1_78p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(13z)^2 η(39z)^(-1) η(78z)`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(13z)^2 η(39z)^(-1) η(78z)` at level 234. -/
abbrev cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1_old_234_1 : gamma0CuspForms 234 :=
  gamma0RescaleToLevel cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1_old_234_1_eq_eta :
    cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1_old_234_1 =
      etaQuotientCuspForm 234 sparse![234; 0 => -1, 1 => 1, 2 => 2, 12 => 2, 38 => -1, 77 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1_old_234_1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1_old_234_1 =
    [0, 0, 0, 1, 1, 1, 0, 0, 1, -1, 0, -1, 0, 0, -1, 0, -4, -3, -1, 0,
     -1, -3, 1, 0, 1, 1, 0, 1, 0, 4, 0, -4, 0, 3, 2, 3, 0, 2, 0, 0,
     4, -1, 3, 7, 3, 2, 0, 3, -1, -1, 0, -5, 1, -4, 3, -8, -5, 6, -4, -5,
     -6, -4, 2, -1, 1, -2, -5, 0, 7, -2, -4, -1, 0, 4, -1, 0, -4, 4, -1, 6,
     -5, -4, 3, -1, 5, 2, -4, 0, -1, 1, 1, 3, 0, 0, -4, -2, 4, -6, 2, 1] := by
  eta_coeff

end WeightTwoCusps
