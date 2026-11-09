module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_1m2_2p4_4m2_5p2_8p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-2) η(5z)^2 η(8z)^2`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-2) η(5z)^2 η(8z)^2` at level 480. -/
abbrev cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_480_1 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_480_1_eq_eta :
    cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_480_1 =
      etaQuotientCuspForm 480 sparse![480; 0 => -2, 1 => 4, 3 => -2, 4 => 2, 7 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_480_1_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_480_1 =
    [0, 1, 2, 1, 2, 4, 2, 1, 4, 3, 0, 2, 0, 0, 2, -1, 0, 2, -2, -4,
     2, -6, -4, 3, -8, -7, 0, -2, -8, 2, -2, -2, 0, -12, -4, -1, -6, -8, 0, -6,
     -4, 4, -4, 1, 8, -6, -10, 1, 0, -1, 2, 2, -4, 8, -4, -2, 8, 0, 4, 0,
     0, -4, 12, 1, 0, 18, 0, 3, 4, 6, 6, 6, 4, -6, 8, 1, 8, 12, 4, 4,
     0, 3, 0, 5, 0, 8, 18, -2, 0, 10, -4, -6, 8, 12, 2, 4, 0, 6, 6, 2] := by
  eta_coeff

end WeightTwoCusps
