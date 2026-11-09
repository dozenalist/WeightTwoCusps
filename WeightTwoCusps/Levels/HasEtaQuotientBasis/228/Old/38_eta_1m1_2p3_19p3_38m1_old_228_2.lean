module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«38».New.«38_eta_1m1_2p3_19p3_38m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(2z)^(-1) η(4z)^3 η(38z)^3 η(76z)^(-1)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_38_eta_1m1_2p3_19p3_38m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^3 η(38z)^3 η(76z)^(-1)` at level 228. -/
abbrev cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_2 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_38_eta_1m1_2p3_19p3_38m1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_2_eq_eta :
    cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_2 =
      etaQuotientCuspForm 228 sparse![228; 1 => -1, 3 => 3, 37 => 3, 75 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_2_first_coeffs :
    first_coeffs 100 cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_2 =
    [0, 0, 1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -2, 0, 1, 0, -1, 0, -1, 0,
     0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0,
     -4, 0, -1, 0, 4, 0, 0, 0, 2, 0, 6, 0, -4, 0, 3, 0, 2, 0, 1, 0,
     -2, 0, -6, 0, 3, 0, -4, 0, -1, 0, -7, 0, -2, 0, 0, 0, 0, 0, 4, 0,
     -6, 0, -6, 0, 0, 0, 3, 0, -2, 0, 5, 0, -1, 0, 3, 0, -3, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
