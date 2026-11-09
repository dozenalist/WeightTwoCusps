module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«136».New.«136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-1) η(17z) η(34z)^(-1) η(68z) η(136z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-1) η(17z) η(34z)^(-1) η(68z) η(136z)` at level 408. -/
abbrev cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_1_eq_eta :
    cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 16 => 1, 33 => -1, 67 => 1, 135 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_old_408_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, -1, 0, 1, -1, 1, 0, -1, -1,
     1, -1, -2, 0, -1, -1, -1, -2, -4, 2, 0, 0, -1, -4, 0, 0, 2, -2, 2, 2,
     -1, 2, -1, -1, 3, 2, -1, -1, -1, 2, 2, 0, 2, 1, 0, 1, 0, 0, -1, 1,
     0, -2, -1, 2, 1, 0, 3, -1, -1, 0, 0, 0, -1, 2, 3, 2, 0, -2, 0, 2,
     -1, 2, -2, 1, 4, 1, 2, -3, 3, -2, -1, -2, -2, 2, 2, -2, -1, 0, -3, 2] := by
  eta_coeff

end WeightTwoCusps
