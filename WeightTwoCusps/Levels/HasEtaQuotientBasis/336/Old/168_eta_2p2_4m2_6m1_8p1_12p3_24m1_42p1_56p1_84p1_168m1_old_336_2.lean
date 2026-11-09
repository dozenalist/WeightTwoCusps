module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«168».New.«168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(4z)^2 η(8z)^(-2) η(12z)^(-1) η(16z) η(24z)^3 η(48z)^(-1) η(84z) η(112z) η(168z) η(336z)^(-1)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(8z)^(-2) η(12z)^(-1) η(16z) η(24z)^3 η(48z)^(-1) η(84z) η(112z) η(168z) η(336z)^(-1)` at level 336. -/
abbrev cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1_old_336_2 : gamma0CuspForms 336 :=
  gamma0Rescale cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1_old_336_2_eq_eta :
    cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1_old_336_2 =
      etaQuotientCuspForm 336 sparse![336; 3 => 2, 7 => -2, 11 => -1, 15 => 1, 23 => 3, 47 => -1, 83 => 1, 111 => 1, 167 => 1, 335 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1_old_336_2_first_coeffs :
    first_coeffs 100 cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1_old_336_2 =
    [0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0,
     0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, -1, 0,
     0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
