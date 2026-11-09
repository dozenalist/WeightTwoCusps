module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».New.«128_eta_2p2_4p1_16p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(4z)^2 η(8z) η(32z)`; see
[the local level table](../../TABLE.md#level-256).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_128_eta_2p2_4p1_16p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(8z) η(32z)` at level 256. -/
abbrev cuspForm_128_eta_2p2_4p1_16p1_old_256_2 : gamma0CuspForms 256 :=
  gamma0Rescale cuspForm_128_eta_2p2_4p1_16p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_128_eta_2p2_4p1_16p1_old_256_2_eq_eta :
    cuspForm_128_eta_2p2_4p1_16p1_old_256_2 =
      etaQuotientCuspForm 256 sparse![256; 3 => 2, 7 => 1, 31 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_128_eta_2p2_4p1_16p1_old_256_2_first_coeffs :
    first_coeffs 100 cuspForm_128_eta_2p2_4p1_16p1_old_256_2 =
    [0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0, 1, 0,
     0, 0, 2, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, -2, 0,
     0, 0, 8, 0, 0, 0, -4, 0, 0, 0, -1, 0, 0, 0, 4, 0, 0, 0, 6, 0,
     0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 8, 0, 0, 0, -10, 0, 0, 0, -4, 0,
     0, 0, -6, 0, 0, 0, -6, 0, 0, 0, -2, 0, 0, 0, 8, 0, 0, 0, 9, 0] := by
  eta_coeff

end WeightTwoCusps
