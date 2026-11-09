module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».New.«48_eta_1m2_2p4_3p2_6m2_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(8z)^(-2) η(16z)^4 η(24z)^2 η(48z)^(-2) η(96z)^2`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(8z)` of `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z)^(-2) η(16z)^4 η(24z)^2 η(48z)^(-2) η(96z)^2` at level 384. -/
abbrev cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_384_8 : gamma0CuspForms 384 :=
  gamma0Rescale cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2 8

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_384_8_eq_eta :
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_384_8 =
      etaQuotientCuspForm 384 sparse![384; 7 => -2, 15 => 4, 23 => 2, 47 => -2, 95 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_384_8_first_coeffs :
    first_coeffs 100 cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_384_8 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
