module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m4_2p10_4m4_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(12z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_144_eta_1m4_2p10_4m4_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(12z)^2` at level 432. -/
abbrev cuspForm_144_eta_1m4_2p10_4m4_12p2_old_432_1 : gamma0CuspForms 432 :=
  gamma0RescaleToLevel cuspForm_144_eta_1m4_2p10_4m4_12p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_144_eta_1m4_2p10_4m4_12p2_old_432_1_eq_eta :
    cuspForm_144_eta_1m4_2p10_4m4_12p2_old_432_1 =
      etaQuotientCuspForm 432 sparse![432; 0 => -4, 1 => 10, 3 => -4, 11 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m4_2p10_4m4_12p2_old_432_1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m4_2p10_4m4_12p2_old_432_1 =
    [0, 1, 4, 4, 0, 4, 8, 0, 0, 4, 4, 8, 0, -2, 0, -8, 0, -4, -8, 4,
     0, 0, -8, -16, 0, -1, -8, 4, 0, -12, -16, -8, 0, -16, -4, 0, 0, 6, -16, -8,
     0, 12, 0, -4, 0, -8, 16, 0, 0, -7, -4, 8, 0, 4, 8, 8, 0, 16, -12, 8,
     0, -2, 32, 0, 0, -8, 32, 4, 0, 32, 0, 16, 0, 10, 24, -4, 0, 0, -16, 8,
     0, 4, 12, -8, 0, -4, 16, 24, 0, 12, 16, 0, 0, -32, 0, 16, 0, 2, -28, -16] := by
  eta_coeff

end WeightTwoCusps
