module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«76».New.«76_eta_1p1_4p1_19m3_38p8_76m3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z) η(4z) η(19z)^(-3) η(38z)^8 η(76z)^(-3)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(4z) η(19z)^(-3) η(38z)^8 η(76z)^(-3)` at level 228. -/
abbrev cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_1 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_1_eq_eta :
    cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_1 =
      etaQuotientCuspForm 228 sparse![228; 0 => 1, 3 => 1, 18 => -3, 37 => 8, 75 => -3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_1_first_coeffs :
    first_coeffs 100 cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_1 =
    [0, 1, -1, -1, 0, -1, 2, 1, 1, -1, 0, 1, -1, -1, -1, 0, -2, 1, 0, 0,
     4, -1, -4, 0, -2, 6, 4, 3, -2, 1, 2, -6, -3, -4, 1, -7, 2, 0, 0, 4,
     6, -6, 0, 3, 2, 5, 1, 3, 3, -2, -9, 1, -3, 3, -6, -1, -3, 0, 0, 7,
     -6, -1, 6, -3, 2, -2, 4, 1, -4, 1, 8, 2, 2, 1, 0, -9, 1, 3, -5, -4,
     -2, -3, 8, 0, 3, -9, 0, 0, 2, 2, -6, -1, 0, 6, -2, 3, 6, 0, 2, 1] := by
  eta_coeff

end WeightTwoCusps
