module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«98».New.«98_eta_1m1_2p2_7p1_14p1_49p2_98m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(z)^(-1) η(2z)^2 η(7z) η(14z) η(49z)^2 η(98z)^(-1)`; see
[the local level table](../../TABLE.md#level-392).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(7z) η(14z) η(49z)^2 η(98z)^(-1)` at level 392. -/
abbrev cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_392_1 : gamma0CuspForms 392 :=
  gamma0RescaleToLevel cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_392_1_eq_eta :
    cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_392_1 =
      etaQuotientCuspForm 392 sparse![392; 0 => -1, 1 => 2, 6 => 1, 13 => 1, 48 => 2, 97 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_392_1_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_392_1 =
    [0, 1, 1, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0, 0, -1, -2, -1, 0, -3, 0,
     0, -2, 2, 0, 0, -1, 0, 0, 1, 0, -2, 0, 1, 0, 0, 0, -1, 4, 0, 2,
     0, 0, 2, 0, 0, 0, 4, 0, 0, 1, -1, -2, 0, -2, 0, 0, -1, 4, 4, 0,
     -2, 0, 0, 1, 5, 0, 0, 6, 0, 0, 0, -2, 3, 0, 0, 0, 0, 0, -2, 2,
     0, -3, 0, 0, -2, -2, -10, 0, -6, 0, 0, -4, 0, -4, 0, -10, 0, 0, -1, -2] := by
  eta_coeff

end WeightTwoCusps
