module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(2z)^(-2) η(4z)^3 η(6z)^3 η(12z)^(-2) η(26z)^3 η(52z)^(-2) η(78z)^(-2) η(156z)^3`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^3 η(6z)^3 η(12z)^(-2) η(26z)^3 η(52z)^(-2) η(78z)^(-2) η(156z)^3` at level 312. -/
abbrev cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_2 : gamma0CuspForms 312 :=
  gamma0RescaleToLevel cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_2_eq_eta :
    cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_2 =
      etaQuotientCuspForm 312 sparse![312; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 25 => 3, 51 => -2, 77 => -2, 155 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_2_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_312_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0,
     -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -3, 0, -2, 0, -3, 0, 1, 0, -2, 0,
     -8, 0, -5, 0, -6, 0, 2, 0, -1, 0, -1, 0, -3, 0, -6, 0, 10, 0, 6, 0,
     7, 0, -2, 0, 0, 0, 12, 0, 0, 0, 11, 0, 1, 0, 0, 0, 4, 0, 2, 0,
     11, 0, -10, 0, -1, 0, 3, 0, 0, 0, -1, 0, -6, 0, 10, 0, -6, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
