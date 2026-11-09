module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«196».New.«196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(2z)^(-1) η(4z)^2 η(14z)^(-1) η(28z)^4 η(56z)^(-1) η(196z)^2 η(392z)^(-1)`; see
[the local level table](../../TABLE.md#level-392).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(14z)^(-1) η(28z)^4 η(56z)^(-1) η(196z)^2 η(392z)^(-1)` at level 392. -/
abbrev cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1_old_392_2 : gamma0CuspForms 392 :=
  gamma0Rescale cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1_old_392_2_eq_eta :
    cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1_old_392_2 =
      etaQuotientCuspForm 392 sparse![392; 1 => -1, 3 => 2, 13 => -1, 27 => 4, 55 => -1, 195 => 2, 391 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1_old_392_2_first_coeffs :
    first_coeffs 100 cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1_old_392_2 =
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 1, 0, -2, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, -1, 0, 2, 0,
     -2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -3, 0, -2, 0, 0, 0, -2, 0,
     0, 0, 0, 0, -2, 0, -2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
