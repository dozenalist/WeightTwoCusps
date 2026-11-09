module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_1m1_2p2_10p2_25p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(2z)^(-1) η(4z)^2 η(20z)^2 η(50z)`; see
[the local level table](../../TABLE.md#level-200).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_100_eta_1m1_2p2_10p2_25p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(20z)^2 η(50z)` at level 200. -/
abbrev cuspForm_100_eta_1m1_2p2_10p2_25p1_old_200_2 : gamma0CuspForms 200 :=
  gamma0Rescale cuspForm_100_eta_1m1_2p2_10p2_25p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_100_eta_1m1_2p2_10p2_25p1_old_200_2_eq_eta :
    cuspForm_100_eta_1m1_2p2_10p2_25p1_old_200_2 =
      etaQuotientCuspForm 200 sparse![200; 1 => -1, 3 => 2, 19 => 2, 49 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_100_eta_1m1_2p2_10p2_25p1_old_200_2_first_coeffs :
    first_coeffs 100 cuspForm_100_eta_1m1_2p2_10p2_25p1_old_200_2 =
    [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, -1, 0, -2, 0, 0, 0, -2, 0, 0, 0, 1, 0, -2, 0, 0, 0,
     0, 0, 0, 0, -3, 0, 0, 0, 0, 0, -1, 0, 0, 0, -3, 0, -2, 0, 0, 0,
     0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 5, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0, 0, 6, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
