module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«140».New.«140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(3z)^(-2) η(6z)^4 η(12z)^(-1) η(15z)^2 η(30z)^(-1) η(42z)^2 η(84z)^(-1) η(210z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^4 η(12z)^(-1) η(15z)^2 η(30z)^(-1) η(42z)^2 η(84z)^(-1) η(210z)` at level 420. -/
abbrev cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_420_3 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_420_3_eq_eta :
    cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_420_3 =
      etaQuotientCuspForm 420 sparse![420; 2 => -2, 5 => 4, 11 => -1, 14 => 2, 29 => -1, 41 => 2, 83 => -1, 209 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_420_3_first_coeffs :
    first_coeffs 100 cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_old_420_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0,
     0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -3, 0, 0, -4, 0, 0, -2, 0, 0,
     -4, 0, 0, -6, 0, 0, 0, 0, 0, -2, 0, 0, -4, 0, 0, 2, 0, 0, -2, 0,
     0, -5, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 2, 0, 0, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
