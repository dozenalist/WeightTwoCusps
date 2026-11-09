module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».New.«64_eta_1m2_2p5_4m2_8p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(4z)^(-2) η(8z)^5 η(16z)^(-2) η(32z)^3`; see
[the local level table](../../TABLE.md#level-256).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_64_eta_1m2_2p5_4m2_8p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^5 η(16z)^(-2) η(32z)^3` at level 256. -/
abbrev cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_4 : gamma0CuspForms 256 :=
  gamma0Rescale cuspForm_64_eta_1m2_2p5_4m2_8p3 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_4_eq_eta :
    cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_4 =
      etaQuotientCuspForm 256 sparse![256; 3 => -2, 7 => 5, 15 => -2, 31 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_4_first_coeffs :
    first_coeffs 100 cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0,
     -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
