module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(3z)^(-2) η(6z)^3 η(9z)^3 η(18z)^(-2) η(39z)^3 η(78z)^(-2) η(117z)^(-2) η(234z)^3`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^3 η(9z)^3 η(18z)^(-2) η(39z)^3 η(78z)^(-2) η(117z)^(-2) η(234z)^3` at level 234. -/
abbrev cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_234_3 : gamma0CuspForms 234 :=
  gamma0Rescale cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_234_3_eq_eta :
    cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_234_3 =
      etaQuotientCuspForm 234 sparse![234; 2 => -2, 5 => 3, 8 => 3, 17 => -2, 38 => 3, 77 => -2, 116 => -2, 233 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_234_3_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_234_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, 2, 0, 0, 2, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, 0, 1, 0, 0, -3, 0, 0, -2, 0, 0, -3, 0, 0, 1, 0, 0, -2, 0, 0,
     -8, 0, 0, -5, 0, 0, -6, 0, 0, 2, 0, 0, -1, 0, 0, -1, 0, 0, -3, 0,
     0, -6, 0, 0, 10, 0, 0, 6, 0, 0, 7, 0, 0, -2, 0, 0, 0, 0, 0, 12] := by
  eta_coeff

end WeightTwoCusps
