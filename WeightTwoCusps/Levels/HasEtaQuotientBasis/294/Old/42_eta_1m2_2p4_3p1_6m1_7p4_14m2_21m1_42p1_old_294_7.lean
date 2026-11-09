module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(7z)^(-2) η(14z)^4 η(21z) η(42z)^(-1) η(49z)^4 η(98z)^(-2) η(147z)^(-1) η(294z)`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z)^(-2) η(14z)^4 η(21z) η(42z)^(-1) η(49z)^4 η(98z)^(-2) η(147z)^(-1) η(294z)` at level 294. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_294_7 : gamma0CuspForms 294 :=
  gamma0Rescale cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_294_7_eq_eta :
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_294_7 =
      etaQuotientCuspForm 294 sparse![294; 6 => -2, 13 => 4, 20 => 1, 41 => -1, 48 => 4, 97 => -2, 146 => -1, 293 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_294_7_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_294_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0,
     0, 0, 0, -8, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, -6, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -4, 0] := by
  eta_coeff

end WeightTwoCusps
