module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(7z)^(-1) η(14z)^2 η(21z)^2 η(42z)^(-1) η(49z)^(-1) η(98z)^2 η(147z)^2 η(294z)^(-1)`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z)^(-1) η(14z)^2 η(21z)^2 η(42z)^(-1) η(49z)^(-1) η(98z)^2 η(147z)^2 η(294z)^(-1)` at level 294. -/
abbrev cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_294_7 : gamma0CuspForms 294 :=
  gamma0Rescale cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_294_7_eq_eta :
    cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_294_7 =
      etaQuotientCuspForm 294 sparse![294; 6 => -1, 13 => 2, 20 => 2, 41 => -1, 48 => -1, 97 => 2, 146 => 2, 293 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_294_7_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_294_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
