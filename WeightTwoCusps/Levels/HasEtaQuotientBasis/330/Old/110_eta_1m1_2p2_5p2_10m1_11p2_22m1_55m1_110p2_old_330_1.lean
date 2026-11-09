module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z)^2 η(5z)^2 η(10z)^(-1) η(11z)^2 η(22z)^(-1) η(55z)^(-1) η(110z)^2`; see
[the local level table](../../TABLE.md#level-330).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(5z)^2 η(10z)^(-1) η(11z)^2 η(22z)^(-1) η(55z)^(-1) η(110z)^2` at level 330. -/
abbrev cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2_old_330_1 : gamma0CuspForms 330 :=
  gamma0RescaleToLevel cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2_old_330_1_eq_eta :
    cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2_old_330_1 =
      etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 10 => 2, 21 => -1, 54 => -1, 109 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2_old_330_1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2_old_330_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -2, -1, 0, -2, 0, 1, -4, -2,
     0, -2, -1, 4, 2, 0, 4, 0, 1, 4, 2, 0, 0, 2, 0, 1, 0, 2, 0, -6,
     -2, -4, 2, 1, 0, 0, -2, 0, -4, 0, 0, 6, 1, -6, 0, 0, -4, -4, -2, -4,
     0, 2, -4, 5, 4, 1, -2, -6, 3, 4, -2, 0, 9, -3, -2, 0, -2, -1, 10, 4,
     -2, 8, 2, -3, 2, 3, 4, 4, 2, 4, 1, 4, 2, 0, -6, -2, -8, -2, -2, 0] := by
  eta_coeff

end WeightTwoCusps
