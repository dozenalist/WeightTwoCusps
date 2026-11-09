module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«224».New.«224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(8z)^(-2) η(16z)^5 η(28z)^2 η(56z)^(-1) η(64z)^(-1) η(112z) η(224z)^(-1) η(448z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z)^(-2) η(16z)^5 η(28z)^2 η(56z)^(-1) η(64z)^(-1) η(112z) η(224z)^(-1) η(448z)` at level 448. -/
abbrev cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1_old_448_2 : gamma0CuspForms 448 :=
  gamma0Rescale cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1_old_448_2_eq_eta :
    cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1_old_448_2 =
      etaQuotientCuspForm 448 sparse![448; 7 => -2, 15 => 5, 27 => 2, 55 => -1, 63 => -1, 111 => 1, 223 => -1, 447 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1_old_448_2_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1_old_448_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, -4, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0,
     0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
