module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m3_2p7_4m2_7p1_14p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(3z)^(-3) η(6z)^7 η(12z)^(-2) η(21z) η(42z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-3) η(6z)^7 η(12z)^(-2) η(21z) η(42z)` at level 336. -/
abbrev cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_336_3 : gamma0CuspForms 336 :=
  gamma0Rescale cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_336_3_eq_eta :
    cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_336_3 =
      etaQuotientCuspForm 336 sparse![336; 2 => -3, 5 => 7, 11 => -2, 20 => 1, 41 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_336_3_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_336_3 =
    [0, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0,
     0, 1, 0, 0, 3, 0, 0, -3, 0, 0, 0, 0, 0, 4, 0, 0, -2, 0, 0, 0,
     0, 0, -1, 0, 0, -4, 0, 0, -3, 0, 0, -2, 0, 0, -5, 0, 0, -10, 0, 0,
     0, 0, 0, -2, 0, 0, -8, 0, 0, 4, 0, 0, -6, 0, 0, -9, 0, 0, 4, 0,
     0, -4, 0, 0, 1, 0, 0, 2, 0, 0, -8, 0, 0, -4, 0, 0, 3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
