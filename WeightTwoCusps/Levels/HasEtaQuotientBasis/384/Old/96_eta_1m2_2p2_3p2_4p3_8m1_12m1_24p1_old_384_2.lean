module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z)^(-2) η(4z)^2 η(6z)^2 η(8z)^3 η(16z)^(-1) η(24z)^(-1) η(48z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^2 η(6z)^2 η(8z)^3 η(16z)^(-1) η(24z)^(-1) η(48z)` at level 384. -/
abbrev cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_384_2 : gamma0CuspForms 384 :=
  gamma0RescaleToLevel cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_384_2_eq_eta :
    cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_384_2 =
      etaQuotientCuspForm 384 sparse![384; 1 => -2, 3 => 2, 5 => 2, 7 => 3, 15 => -1, 23 => -1, 47 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_384_2_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_384_2 =
    [0, 0, 1, 0, 2, 0, 3, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0,
     -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, -6, 0, 0, 0, -6, 0, 2, 0, 0, 0,
     -8, 0, -4, 0, -8, 0, 0, 0, 0, 0, -1, 0, -4, 0, -9, 0, 0, 0, 2, 0,
     -4, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 4, 0, -2, 0, 8, 0, 18, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 16, 0, 2, 0, 16, 0, 0, 0, 0, 0, 9, 0] := by
  eta_coeff

end WeightTwoCusps
