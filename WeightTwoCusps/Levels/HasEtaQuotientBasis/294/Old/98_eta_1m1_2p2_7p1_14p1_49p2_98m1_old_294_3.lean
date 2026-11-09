module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«98».New.«98_eta_1m1_2p2_7p1_14p1_49p2_98m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(3z)^(-1) η(6z)^2 η(21z) η(42z) η(147z)^2 η(294z)^(-1)`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(21z) η(42z) η(147z)^2 η(294z)^(-1)` at level 294. -/
abbrev cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_294_3 : gamma0CuspForms 294 :=
  gamma0Rescale cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_294_3_eq_eta :
    cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_294_3 =
      etaQuotientCuspForm 294 sparse![294; 2 => -1, 5 => 2, 20 => 1, 41 => 1, 146 => 2, 293 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_294_3_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_1m1_2p2_7p1_14p1_49p2_98m1_old_294_3 =
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -1, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0,
     0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
