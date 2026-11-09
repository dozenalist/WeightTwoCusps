module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».New.«128_eta_2p2_4p1_16p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(6z)^2 η(12z) η(48z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_128_eta_2p2_4p1_16p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^2 η(12z) η(48z)` at level 384. -/
abbrev cuspForm_128_eta_2p2_4p1_16p1_old_384_3 : gamma0CuspForms 384 :=
  gamma0Rescale cuspForm_128_eta_2p2_4p1_16p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_128_eta_2p2_4p1_16p1_old_384_3_eq_eta :
    cuspForm_128_eta_2p2_4p1_16p1_old_384_3 =
      etaQuotientCuspForm 384 sparse![384; 5 => 2, 11 => 1, 47 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_128_eta_2p2_4p1_16p1_old_384_3_first_coeffs :
    first_coeffs 100 cuspForm_128_eta_2p2_4p1_16p1_old_384_3 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0,
     0, 0, 0, 8, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
