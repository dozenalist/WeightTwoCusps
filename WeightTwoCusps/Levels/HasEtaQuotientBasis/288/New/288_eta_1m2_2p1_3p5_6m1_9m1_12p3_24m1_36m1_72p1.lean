module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(6z)^(-1) η(9z)^(-1) η(12z)^3 η(24z)^(-1) η(36z)^(-1) η(72z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(6z)^(-1) η(9z)^(-1) η(12z)^3 η(24z)^(-1) η(36z)^(-1) η(72z)` at level 288. -/
abbrev cuspForm_288_eta_1m2_2p1_3p5_6m1_9m1_12p3_24m1_36m1_72p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 1, 2 => 5, 5 => -1, 8 => -1, 11 => 3, 23 => -1, 35 => -1, 71 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m2_2p1_3p5_6m1_9m1_12p3_24m1_36m1_72p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m2_2p1_3p5_6m1_9m1_12p3_24m1_36m1_72p1 =
    [0, 0, 1, 2, 4, 3, 4, 4, 6, 6, 4, 8, 8, 12, 6, 4, 0, 3, 4, 4,
     -2, 0, 8, 0, 0, -12, 4, 2, 0, 3, -8, -4, 0, 0, -4, -16, -8, 0, -14, -4,
     0, -9, 0, -4, 4, -12, -16, 16, 0, 0, -7, -12, -8, -9, 4, -8, -24, 0, -12, -8,
     -16, 0, 10, -8, 0, -6, -16, -4, 2, 0, 0, -32, 0, -12, -18, -2, -16, 0, -8, -4,
     0, -18, 12, 24, 0, -36, -10, 4, 0, 3, -8, -8, -8, 0, 0, -16, 0, 36, 17, 8] := by
  eta_coeff

end WeightTwoCusps
