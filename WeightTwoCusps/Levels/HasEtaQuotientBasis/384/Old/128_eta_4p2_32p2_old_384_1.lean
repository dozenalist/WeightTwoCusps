module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».New.«128_eta_4p2_32p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(4z)^2 η(32z)^2`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_128_eta_4p2_32p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(32z)^2` at level 384. -/
abbrev cuspForm_128_eta_4p2_32p2_old_384_1 : gamma0CuspForms 384 :=
  gamma0RescaleToLevel cuspForm_128_eta_4p2_32p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_128_eta_4p2_32p2_old_384_1_eq_eta :
    cuspForm_128_eta_4p2_32p2_old_384_1 =
      etaQuotientCuspForm 384 sparse![384; 3 => 2, 31 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_128_eta_4p2_32p2_old_384_1_first_coeffs :
    first_coeffs 100 cuspForm_128_eta_4p2_32p2_old_384_1 =
    [0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 1,
     0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 2,
     0, 0, 0, 3, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 7,
     0, 0, 0, -2, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, -1, 0, 0, 0, -4,
     0, 0, 0, -3, 0, 0, 0, -6, 0, 0, 0, -4, 0, 0, 0, 2, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
