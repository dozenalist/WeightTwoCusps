module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».New.«64_eta_1m2_2p5_4m2_8p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^3`; see
[the local level table](../../TABLE.md#level-256).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_64_eta_1m2_2p5_4m2_8p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^3` at level 256. -/
abbrev cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_1 : gamma0CuspForms 256 :=
  gamma0RescaleToLevel cuspForm_64_eta_1m2_2p5_4m2_8p3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_1_eq_eta :
    cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_1 =
      etaQuotientCuspForm 256 sparse![256; 0 => -2, 1 => 5, 3 => -2, 7 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_1_first_coeffs :
    first_coeffs 100 cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_1 =
    [0, 1, 2, 0, 0, 2, 0, 0, 0, -3, -4, 0, 0, -6, 0, 0, 0, 2, -6, 0,
     0, 0, 0, 0, 0, -1, 12, 0, 0, 10, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0,
     0, 10, 0, 0, 0, -6, 0, 0, 0, -7, -2, 0, 0, -14, 0, 0, 0, 0, -20, 0,
     0, 10, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, -6, -4, 0, 0, 0, 0, 0,
     0, 9, 20, 0, 0, 4, 0, 0, 0, 10, 12, 0, 0, 0, 0, 0, 0, 18, -14, 0] := by
  eta_coeff

end WeightTwoCusps
