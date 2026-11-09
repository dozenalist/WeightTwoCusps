module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(16z)^2 η(32z)^(-1) η(112z) η(224z)`; see
[the local level table](../../TABLE.md#level-224).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(16z)^2 η(32z)^(-1) η(112z) η(224z)` at level 224. -/
abbrev cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_224_2 : gamma0CuspForms 224 :=
  gamma0Rescale cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_224_2_eq_eta :
    cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_224_2 =
      etaQuotientCuspForm 224 sparse![224; 1 => -2, 3 => 5, 7 => -2, 15 => 2, 31 => -1, 111 => 1, 223 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_224_2_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_224_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 0, -4, 0,
     0, 0, 0, 0, 0, 0, 2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0,
     0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
