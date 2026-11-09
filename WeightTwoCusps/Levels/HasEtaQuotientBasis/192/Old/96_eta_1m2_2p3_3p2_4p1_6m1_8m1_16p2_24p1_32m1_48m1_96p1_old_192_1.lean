module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)`; see
[the local level table](../../TABLE.md#level-192).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)` at level 192. -/
abbrev cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1_old_192_1 : gamma0CuspForms 192 :=
  gamma0RescaleToLevel cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1_old_192_1_eq_eta :
    cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1_old_192_1 =
      etaQuotientCuspForm 192 sparse![192; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -1, 7 => -1, 15 => 2, 23 => 1, 31 => -1, 47 => -1, 95 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1_old_192_1_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1_old_192_1 =
    [0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 2, -2, 0, 0, -2, 0, -4, 0, -2,
     -4, -2, -8, -4, 0, 0, 0, -5, 0, -2, -4, 4, 0, 4, 0, 0, 2, -4, 8, 10,
     0, 4, 0, 2, 8, 2, 16, 0, 0, 8, 0, 2, -4, 6, 2, -4, 0, -4, 0, 2,
     4, 4, -16, 0, 0, -4, 0, -2, 4, -4, 0, 4, 0, -8, 0, -1, -8, -8, -4, -4,
     0, 0, 0, -2, 0, -4, -8, -18, 0, 8, 0, 0, -16, 6, 0, 4, 0, -8, 0, 2] := by
  eta_coeff

end WeightTwoCusps
