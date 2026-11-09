module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».New.«72_eta_1m1_3p3_4p1_12p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-1) η(3z)^3 η(4z) η(12z)`; see
[the local level table](../../TABLE.md#level-144).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_72_eta_1m1_3p3_4p1_12p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(4z) η(12z)` at level 144. -/
abbrev cuspForm_72_eta_1m1_3p3_4p1_12p1_old_144_1 : gamma0CuspForms 144 :=
  gamma0RescaleToLevel cuspForm_72_eta_1m1_3p3_4p1_12p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_72_eta_1m1_3p3_4p1_12p1_old_144_1_eq_eta :
    cuspForm_72_eta_1m1_3p3_4p1_12p1_old_144_1 =
      etaQuotientCuspForm 144 sparse![144; 0 => -1, 2 => 3, 3 => 1, 11 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_72_eta_1m1_3p3_4p1_12p1_old_144_1_first_coeffs :
    first_coeffs 100 cuspForm_72_eta_1m1_3p3_4p1_12p1_old_144_1 =
    [0, 1, 1, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -2, -4, -4, 0, -1, 0, -4,
     0, 0, 0, 4, 0, -1, 2, 2, 0, -3, 0, 8, 0, 8, 0, 0, 0, 6, 8, -4,
     0, 3, 0, 4, 0, 4, 0, 0, 0, -7, -5, 4, 0, 1, 0, -8, 0, -8, 0, -2,
     0, -2, -4, 0, 0, -2, 0, -4, 0, -16, 0, -4, 0, 10, -10, -2, 0, 0, 0, -8,
     0, -2, 0, 2, 0, -4, 8, 12, 0, 3, 0, 0, 0, 16, 0, -4, 0, 2, 9, -8] := by
  eta_coeff

end WeightTwoCusps
