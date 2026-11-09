module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^2 η(16z)^(-1) η(56z) η(112z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^2 η(16z)^(-1) η(56z) η(112z)` at level 448. -/
abbrev cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_1 : gamma0CuspForms 448 :=
  gamma0RescaleToLevel cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_1_eq_eta :
    cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_1 =
      etaQuotientCuspForm 448 sparse![448; 0 => -2, 1 => 5, 3 => -2, 7 => 2, 15 => -1, 55 => 1, 111 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_1_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_old_448_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, -2, -2, 0, 0, -4,
     0, 0, 0, 2, -4, 0, 0, 0, 0, 0, 0, -4, 2, 0, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 6, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0, 0, 4, 2, 0, 0, 0,
     0, 0, 0, -1, -2, 0, 0, -2, 0, 0, 0, 4, 2, 0, 0, 8, 0, 0, 0, -8,
     0, 0, 0, -4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -6, -4, 0, 0, -6] := by
  eta_coeff

end WeightTwoCusps
