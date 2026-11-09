module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_2p1_5m1_10p2_11p2_22m1_55p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(2z) η(5z)^(-1) η(10z)^2 η(11z)^2 η(22z)^(-1) η(55z)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(5z)^(-1) η(10z)^2 η(11z)^2 η(22z)^(-1) η(55z)` at level 440. -/
abbrev cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1_old_440_1 : gamma0CuspForms 440 :=
  gamma0RescaleToLevel cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1_old_440_1_eq_eta :
    cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1_old_440_1 =
      etaQuotientCuspForm 440 sparse![440; 1 => 1, 4 => -1, 9 => 2, 10 => 2, 21 => -1, 54 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1_old_440_1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1_old_440_1 =
    [0, 0, 0, 1, 0, -1, 0, -1, 1, 0, -1, 0, -1, 1, -2, 0, 2, 1, 4, -2,
     -1, 2, 0, 2, -2, 0, 0, -1, -1, -4, 0, 2, 0, 0, 0, -1, 0, -1, 1, -2,
     0, 0, -1, 1, 0, 0, 2, 4, 1, 0, 0, -2, 3, 3, -4, 0, -2, 0, -5, 2,
     2, 2, 6, -3, -4, 1, 0, 2, 3, 2, 1, -6, 1, -7, 2, 1, -2, 0, -4, 0,
     -1, -4, -2, -1, 6, 1, -4, 2, -1, 0, 1, 6, 0, 1, 6, 0, 0, 4, -2, 2] := by
  eta_coeff

end WeightTwoCusps
