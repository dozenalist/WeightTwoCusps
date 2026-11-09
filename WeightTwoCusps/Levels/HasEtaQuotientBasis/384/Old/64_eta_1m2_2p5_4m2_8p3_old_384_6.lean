module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».New.«64_eta_1m2_2p5_4m2_8p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(6z)^(-2) η(12z)^5 η(24z)^(-2) η(48z)^3`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_64_eta_1m2_2p5_4m2_8p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-2) η(12z)^5 η(24z)^(-2) η(48z)^3` at level 384. -/
abbrev cuspForm_64_eta_1m2_2p5_4m2_8p3_old_384_6 : gamma0CuspForms 384 :=
  gamma0Rescale cuspForm_64_eta_1m2_2p5_4m2_8p3 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_384_6_eq_eta :
    cuspForm_64_eta_1m2_2p5_4m2_8p3_old_384_6 =
      etaQuotientCuspForm 384 sparse![384; 5 => -2, 11 => 5, 23 => -2, 47 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_384_6_first_coeffs :
    first_coeffs 100 cuspForm_64_eta_1m2_2p5_4m2_8p3_old_384_6 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
