module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«150».New.«150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z)^(-1) η(2z)^2 η(10z) η(25z) η(30z) η(50z)^(-1) η(150z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(10z) η(25z) η(30z) η(50z)^(-1) η(150z)` at level 450. -/
abbrev cuspForm_150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1_old_450_1 : gamma0CuspForms 450 :=
  gamma0RescaleToLevel cuspForm_150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1_old_450_1_eq_eta :
    cuspForm_150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1_old_450_1 =
      etaQuotientCuspForm 450 sparse![450; 0 => -1, 1 => 2, 9 => 1, 24 => 1, 29 => 1, 49 => -1, 149 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1_old_450_1_first_coeffs :
    first_coeffs 100 cuspForm_150_eta_1m1_2p2_10p1_25p1_30p1_50m1_150p1_old_450_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, -1, 0,
     -1, 0, 1, -1, 0, 0, 0, -2, 0, 0, -1, 0, -2, -2, 0, 0, 0, -2, -3, 0,
     -1, 0, -1, 1, 0, 0, 0, -1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 4, 2, 0,
     1, 0, 3, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 4, 0,
     3, 0, -7, 0, 0, 0, 0, 1, -3, 0, 1, 0, 1, 2, 0, 0, 0, -1, 5, 0] := by
  eta_coeff

end WeightTwoCusps
