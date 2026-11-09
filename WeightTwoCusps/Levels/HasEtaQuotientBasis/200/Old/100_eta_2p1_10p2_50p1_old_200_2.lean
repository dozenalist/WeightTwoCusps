module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_2p1_10p2_50p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(4z) η(20z)^2 η(100z)`; see
[the local level table](../../TABLE.md#level-200).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_100_eta_2p1_10p2_50p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(20z)^2 η(100z)` at level 200. -/
abbrev cuspForm_100_eta_2p1_10p2_50p1_old_200_2 : gamma0CuspForms 200 :=
  gamma0Rescale cuspForm_100_eta_2p1_10p2_50p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_100_eta_2p1_10p2_50p1_old_200_2_eq_eta :
    cuspForm_100_eta_2p1_10p2_50p1_old_200_2 =
      etaQuotientCuspForm 200 sparse![200; 3 => 1, 19 => 2, 99 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_100_eta_2p1_10p2_50p1_old_200_2_first_coeffs :
    first_coeffs 100 cuspForm_100_eta_2p1_10p2_50p1_old_200_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 0, 0, 0, -1, 0, 0, 0, 3, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
