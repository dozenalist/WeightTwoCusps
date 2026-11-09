module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m2_2p4_7p2_14m2_28p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(4z)^(-2) η(8z)^4 η(28z)^2 η(56z)^(-2) η(112z)^2`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^4 η(28z)^2 η(56z)^(-2) η(112z)^2` at level 448. -/
abbrev cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_448_4 : gamma0CuspForms 448 :=
  gamma0Rescale cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_448_4_eq_eta :
    cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_448_4 =
      etaQuotientCuspForm 448 sparse![448; 3 => -2, 7 => 4, 27 => 2, 55 => -2, 111 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_448_4_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_448_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0,
     2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0,
     -4, 0, 0, 0, -3, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -6, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
