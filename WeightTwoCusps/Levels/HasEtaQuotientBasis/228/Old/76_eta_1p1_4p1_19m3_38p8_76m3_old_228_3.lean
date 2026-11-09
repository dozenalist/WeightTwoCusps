module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«76».New.«76_eta_1p1_4p1_19m3_38p8_76m3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(3z) η(12z) η(57z)^(-3) η(114z)^8 η(228z)^(-3)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(12z) η(57z)^(-3) η(114z)^8 η(228z)^(-3)` at level 228. -/
abbrev cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_3 : gamma0CuspForms 228 :=
  gamma0Rescale cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_3_eq_eta :
    cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_3 =
      etaQuotientCuspForm 228 sparse![228; 2 => 1, 11 => 1, 56 => -3, 113 => 8, 227 => -3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_3_first_coeffs :
    first_coeffs 100 cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_old_228_3 =
    [0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 2, 0,
     0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1,
     0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     4, 0, 0, -1, 0, 0, -4, 0, 0, 0, 0, 0, -2, 0, 0, 6, 0, 0, 4, 0,
     0, 3, 0, 0, -2, 0, 0, 1, 0, 0, 2, 0, 0, -6, 0, 0, -3, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
