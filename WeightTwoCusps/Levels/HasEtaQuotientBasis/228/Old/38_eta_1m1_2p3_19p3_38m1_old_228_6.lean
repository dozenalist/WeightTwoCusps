module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«38».New.«38_eta_1m1_2p3_19p3_38m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(6z)^(-1) η(12z)^3 η(114z)^3 η(228z)^(-1)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_38_eta_1m1_2p3_19p3_38m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z)^3 η(114z)^3 η(228z)^(-1)` at level 228. -/
abbrev cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_6 : gamma0CuspForms 228 :=
  gamma0Rescale cuspForm_38_eta_1m1_2p3_19p3_38m1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_6_eq_eta :
    cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_6 =
      etaQuotientCuspForm 228 sparse![228; 5 => -1, 11 => 3, 113 => 3, 227 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_6_first_coeffs :
    first_coeffs 100 cuspForm_38_eta_1m1_2p3_19p3_38m1_old_228_6 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
