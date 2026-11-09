module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«200».New.«200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z) η(4z)^2 η(5z) η(8z)^(-1) η(40z) η(50z)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^2 η(5z) η(8z)^(-1) η(40z) η(50z)` at level 400. -/
abbrev cuspForm_200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1_old_400_1 : gamma0CuspForms 400 :=
  gamma0RescaleToLevel cuspForm_200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1_old_400_1_eq_eta :
    cuspForm_200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1_old_400_1 =
      etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 7 => -1, 39 => 1, 49 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1_old_400_1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m1_2p1_4p2_5p1_8m1_40p1_50p1_old_400_1 =
    [0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 1, 0, 0, 2, 0, -1, 1, -2, 0, 0,
     0, 0, 0, 0, -1, 0, -2, 0, 0, 0, -2, 0, 0, -2, 1, -1, -2, 0, 0, 0,
     0, 0, 0, -2, -3, -1, 0, -4, 0, 0, -1, 0, 0, -4, -3, 2, -2, 0, 0, 0,
     0, 0, 0, -2, 1, 0, -1, 2, 0, 0, 2, 0, 0, 4, 0, 1, 5, 2, 0, 0,
     0, 0, 0, 6, 2, -2, 2, -2, 0, 0, 1, 0, 0, 2, 6, 0, -1, 8, 0, 0] := by
  eta_coeff

end WeightTwoCusps
