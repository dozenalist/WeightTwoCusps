module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«38».New.«38_eta_1p3_2m1_19m1_38p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(2z)^3 η(4z)^(-1) η(38z)^(-1) η(76z)^3`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_38_eta_1p3_2m1_19m1_38p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^3 η(4z)^(-1) η(38z)^(-1) η(76z)^3` at level 228. -/
abbrev cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_2 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_38_eta_1p3_2m1_19m1_38p3 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_2_eq_eta :
    cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_2 =
      etaQuotientCuspForm 228 sparse![228; 1 => 3, 3 => -1, 37 => -1, 75 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_2_first_coeffs :
    first_coeffs 100 cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -3, 0, 1, 0, 2, 0, 2, 0, -1, 0,
     -4, 0, 1, 0, -2, 0, 0, 0, 2, 0, 4, 0, -1, 0, 2, 0, -2, 0, -1, 0,
     0, 0, -2, 0, -2, 0, -1, 0, -3, 0, 5, 0, 3, 0, 2, 0, 1, 0, -6, 0,
     6, 0, -2, 0, -2, 0, 2, 0, 4, 0, -5, 0, 0, 0, -2, 0, -1, 0, -3, 0,
     2, 0, -2, 0, -3, 0, 1, 0, 4, 0, 3, 0, 0, 0, 5, 0, 2, 0, 4, 0] := by
  eta_coeff

end WeightTwoCusps
