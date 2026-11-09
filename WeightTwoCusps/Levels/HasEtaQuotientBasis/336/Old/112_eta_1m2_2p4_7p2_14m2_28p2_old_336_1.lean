module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m2_2p4_7p2_14m2_28p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(z)^(-2) η(2z)^4 η(7z)^2 η(14z)^(-2) η(28z)^2`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(7z)^2 η(14z)^(-2) η(28z)^2` at level 336. -/
abbrev cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_336_1 : gamma0CuspForms 336 :=
  gamma0RescaleToLevel cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_336_1_eq_eta :
    cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_336_1 =
      etaQuotientCuspForm 336 sparse![336; 0 => -2, 1 => 4, 6 => 2, 13 => -2, 27 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_336_1_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2_old_336_1 =
    [0, 0, 1, 2, 1, 2, 2, 0, 3, 0, -4, 0, -2, -2, 1, -4, -3, 4, 1, -2,
     0, -2, 0, 4, -6, -8, 0, -4, 1, -4, -8, 4, 3, 0, -2, -2, 1, 4, -2, -4,
     0, 4, 2, 0, 0, 2, 8, 4, 6, 0, 11, 4, -4, 8, -4, 0, 3, 0, 2, 6,
     0, 2, 4, 0, -3, 0, 0, -4, 6, -8, -4, 0, 3, 8, -6, 6, 2, 0, 0, -8,
     0, 0, -2, 6, -2, -4, 8, -4, 0, -8, -4, 2, 0, 0, -4, 4, -6, -4, 1, 0] := by
  eta_coeff

end WeightTwoCusps
