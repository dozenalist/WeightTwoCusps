module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».New.«48_eta_1m2_2p4_3p2_6m2_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(7z)^(-2) η(14z)^4 η(21z)^2 η(42z)^(-2) η(84z)^2`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z)^(-2) η(14z)^4 η(21z)^2 η(42z)^(-2) η(84z)^2` at level 336. -/
abbrev cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_336_7 : gamma0CuspForms 336 :=
  gamma0Rescale cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_336_7_eq_eta :
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_336_7 =
      etaQuotientCuspForm 336 sparse![336; 6 => -2, 13 => 4, 20 => 2, 41 => -2, 83 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_336_7_first_coeffs :
    first_coeffs 100 cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_336_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, -4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
