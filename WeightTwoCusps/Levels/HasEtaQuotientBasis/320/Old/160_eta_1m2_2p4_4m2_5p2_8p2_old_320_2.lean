module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_1m2_2p4_4m2_5p2_8p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(2z)^(-2) η(4z)^4 η(8z)^(-2) η(10z)^2 η(16z)^2`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(8z)^(-2) η(10z)^2 η(16z)^2` at level 320. -/
abbrev cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_320_2 : gamma0CuspForms 320 :=
  gamma0Rescale cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_320_2_eq_eta :
    cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_320_2 =
      etaQuotientCuspForm 320 sparse![320; 1 => -2, 3 => 4, 7 => -2, 9 => 2, 15 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_320_2_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_old_320_2 =
    [0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 4, 0, 2, 0, 1, 0, 4, 0, 3, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 2, 0, -1, 0, 0, 0, 2, 0, -2, 0, -4, 0,
     2, 0, -6, 0, -4, 0, 3, 0, -8, 0, -7, 0, 0, 0, -2, 0, -8, 0, 2, 0,
     -2, 0, -2, 0, 0, 0, -12, 0, -4, 0, -1, 0, -6, 0, -8, 0, 0, 0, -6, 0,
     -4, 0, 4, 0, -4, 0, 1, 0, 8, 0, -6, 0, -10, 0, 1, 0, 0, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
