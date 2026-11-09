module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«136».New.«136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(3z)^(-1) η(6z) η(12z)^3 η(24z)^(-1) η(51z) η(102z)^(-1) η(204z) η(408z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(12z)^3 η(24z)^(-1) η(51z) η(102z)^(-1) η(204z) η(408z)` at level 408. -/
abbrev cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_3 : gamma0CuspForms 408 :=
  gamma0Rescale cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_3_eq_eta :
    cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_3 =
      etaQuotientCuspForm 408 sparse![408; 2 => -1, 5 => 1, 11 => 3, 23 => -1, 50 => 1, 101 => -1, 203 => 1, 407 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_3_first_coeffs :
    first_coeffs 100 cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, -1, 0, 0, 0,
     0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0,
     1, 0, 0, -1, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0,
     0, -2, 0, 0, -4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
