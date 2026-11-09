module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(4z)^(-2) η(8z)^5 η(16z)^(-2) η(32z)^2 η(64z)^(-1) η(224z) η(448z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^5 η(16z)^(-2) η(32z)^2 η(64z)^(-1) η(224z) η(448z)` at level 448. -/
abbrev cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_4 : gamma0CuspForms 448 :=
  gamma0Rescale cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_4_eq_eta :
    cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_4 =
      etaQuotientCuspForm 448 sparse![448; 3 => -2, 7 => 5, 15 => -2, 31 => 2, 63 => -1, 223 => 1, 447 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_4_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
