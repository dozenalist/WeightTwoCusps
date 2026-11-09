module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(4z)^(-2) η(8z)^3 η(12z)^3 η(24z)^(-2) η(52z)^3 η(104z)^(-2) η(156z)^(-2) η(312z)^3`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^3 η(12z)^3 η(24z)^(-2) η(52z)^3 η(104z)^(-2) η(156z)^(-2) η(312z)^3` at level 312. -/
abbrev cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_4 : gamma0CuspForms 312 :=
  gamma0Rescale cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_4_eq_eta :
    cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_4 =
      etaQuotientCuspForm 312 sparse![312; 3 => -2, 7 => 3, 11 => 3, 23 => -2, 51 => 3, 103 => -2, 155 => -2, 311 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_4_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
     -3, 0, 0, 0, -2, 0, 0, 0, -3, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0,
     -8, 0, 0, 0, -5, 0, 0, 0, -6, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
