module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».New.«48_eta_1m2_2p4_3p2_6m2_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 96

The eta expression is `η(2z)^(-2) η(4z)^4 η(6z)^2 η(12z)^(-2) η(24z)^2`; see
[the local level table](../../TABLE.md#level-96).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(6z)^2 η(12z)^(-2) η(24z)^2` at level 96. -/
abbrev cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2 : gamma0CuspForms 96 :=
  gamma0Rescale cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2_eq_eta :
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2 =
      etaQuotientCuspForm 96 sparse![96; 1 => -2, 3 => 4, 5 => 2, 11 => -2, 23 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2_first_coeffs :
    first_coeffs 100 cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2 =
    [0, 0, 1, 0, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 0, 1, 0,
     -4, 0, -4, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 2, 0, 2, 0, 4, 0,
     0, 0, 0, 0, 8, 0, 8, 0, 0, 0, -1, 0, -4, 0, 1, 0, 0, 0, 6, 0,
     4, 0, -8, 0, 0, 0, -4, 0, 4, 0, 0, 0, 0, 0, 6, 0, -8, 0, -2, 0,
     0, 0, -6, 0, 0, 0, -4, 0, 0, 0, -2, 0, -16, 0, 0, 0, 0, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
