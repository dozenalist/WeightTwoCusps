module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«150».New.«150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(15z) η(25z)^2 η(50z)^(-1)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(15z) η(25z)^2 η(50z)^(-1)` at level 450. -/
abbrev cuspForm_150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1_old_450_1 : gamma0CuspForms 450 :=
  gamma0RescaleToLevel cuspForm_150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1_old_450_1_eq_eta :
    cuspForm_150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1_old_450_1 =
      etaQuotientCuspForm 450 sparse![450; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => 1, 24 => 2, 49 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1_old_450_1_first_coeffs :
    first_coeffs 100 cuspForm_150_eta_1m1_2p1_3p1_5p1_15p1_25p2_50m1_old_450_1 =
    [0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, -1, 0, -1, 0,
     -1, -2, 0, 0, -1, -1, -2, -3, -2, -2, -3, -2, -3, -4, -4, -4, 1, -2, -2, -2,
     -3, 2, -2, 2, 0, 1, 2, 0, 1, -1, 3, 0, 2, -2, 1, 0, 0, 8, 4, 4,
     3, -2, 0, 4, 5, 2, -2, 4, 0, 2, 4, 4, -1, -2, 6, -1, 0, 0, 6, 2,
     7, 1, -4, 2, -2, 6, 0, 0, 0, -2, 1, 4, 4, 2, -2, -4, 1, 2, 1, 0] := by
  eta_coeff

end WeightTwoCusps
