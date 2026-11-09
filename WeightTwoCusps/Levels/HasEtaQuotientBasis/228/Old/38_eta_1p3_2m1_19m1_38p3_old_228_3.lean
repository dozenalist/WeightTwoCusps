module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«38».New.«38_eta_1p3_2m1_19m1_38p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(3z)^3 η(6z)^(-1) η(57z)^(-1) η(114z)^3`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_38_eta_1p3_2m1_19m1_38p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^3 η(6z)^(-1) η(57z)^(-1) η(114z)^3` at level 228. -/
abbrev cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_3 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_38_eta_1p3_2m1_19m1_38p3 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_3_eq_eta :
    cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_3 =
      etaQuotientCuspForm 228 sparse![228; 2 => 3, 5 => -1, 56 => -1, 113 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_3_first_coeffs :
    first_coeffs 100 cuspForm_38_eta_1p3_2m1_19m1_38p3_old_228_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -3, 0, 0, 1, 0,
     0, 2, 0, 0, 2, 0, 0, -1, 0, 0, -4, 0, 0, 1, 0, 0, -2, 0, 0, 0,
     0, 0, 2, 0, 0, 4, 0, 0, -1, 0, 0, 2, 0, 0, -2, 0, 0, -1, 0, 0,
     0, 0, 0, -2, 0, 0, -2, 0, 0, -1, 0, 0, -3, 0, 0, 5, 0, 0, 3, 0,
     0, 2, 0, 0, 1, 0, 0, -6, 0, 0, 6, 0, 0, -2, 0, 0, -2, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
