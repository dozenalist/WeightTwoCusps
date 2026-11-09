module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_2p1_3p1_13p1_78p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(4z) η(6z) η(26z) η(156z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_78_eta_2p1_3p1_13p1_78p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(6z) η(26z) η(156z)` at level 312. -/
abbrev cuspForm_78_eta_2p1_3p1_13p1_78p1_old_312_2 : gamma0CuspForms 312 :=
  gamma0RescaleToLevel cuspForm_78_eta_2p1_3p1_13p1_78p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_2p1_3p1_13p1_78p1_old_312_2_eq_eta :
    cuspForm_78_eta_2p1_3p1_13p1_78p1_old_312_2 =
      etaQuotientCuspForm 312 sparse![312; 3 => 1, 5 => 1, 25 => 1, 155 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_2p1_3p1_13p1_78p1_old_312_2_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_2p1_3p1_13p1_78p1_old_312_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 1, 0,
     -1, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 1, 0, 2, 0,
     0, 0, -1, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, -3, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 2, 0, 1, 0, -2, 0, 1, 0,
     -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 2, 0, 0, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
