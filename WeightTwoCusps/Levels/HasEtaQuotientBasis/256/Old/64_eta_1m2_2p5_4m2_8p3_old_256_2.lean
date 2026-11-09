module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».New.«64_eta_1m2_2p5_4m2_8p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(16z)^3`; see
[the local level table](../../TABLE.md#level-256).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_64_eta_1m2_2p5_4m2_8p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(16z)^3` at level 256. -/
abbrev cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_2 : gamma0CuspForms 256 :=
  gamma0RescaleToLevel cuspForm_64_eta_1m2_2p5_4m2_8p3 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_2_eq_eta :
    cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_2 =
      etaQuotientCuspForm 256 sparse![256; 1 => -2, 3 => 5, 7 => -2, 15 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_2_first_coeffs :
    first_coeffs 100 cuspForm_64_eta_1m2_2p5_4m2_8p3_old_256_2 =
    [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -3, 0,
     -4, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 2, 0, -6, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 12, 0, 0, 0, 0, 0, 10, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
     0, 0, 10, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
