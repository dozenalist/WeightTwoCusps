module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(6z)^(-1) η(12z)^2 η(18z) η(36z)^(-1) η(39z) η(117z)^(-1) η(234z) η(468z)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(6z)^(-1) η(12z)^2 η(18z) η(36z)^(-1) η(39z) η(117z)^(-1) η(234z) η(468z)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p5_4m2_6m1_12p2_18p1_36m1_39p1_117m1_234p1_468p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 11 => 2, 17 => 1, 35 => -1, 38 => 1, 116 => -1, 233 => 1, 467 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p5_4m2_6m1_12p2_18p1_36m1_39p1_117m1_234p1_468p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p5_4m2_6m1_12p2_18p1_36m1_39p1_117m1_234p1_468p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1, 2, 0, 2, 2, 0, 0, 0,
     0, 2, 2, 0, 0, 0, 0, 0, 2, 0, -1, 0, 0, 0, -2, 0, 0, 2, 0, -2,
     0, 0, 2, 0, 0, -1, -4, 0, 2, -2, 0, -1, -2, 0, -2, -2, 0, 0, 0, 0,
     -4, -4, 0, 0, -4, 0, -2, -2, 0, -3, 2, 0, 0, 2, 0, 0, -4, 0, 2, -2] := by
  eta_coeff

end WeightTwoCusps
