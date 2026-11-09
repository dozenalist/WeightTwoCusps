module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-3) η(8z)^2 η(9z)^(-2) η(16z)^(-1) η(18z) η(36z)^2 η(48z) η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-3) η(8z)^2 η(9z)^(-2) η(16z)^(-1) η(18z) η(36z)^2 η(48z) η(72z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m2_2p1_3p6_6m3_8p2_9m2_16m1_18p1_36p2_48p1_72m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 1, 2 => 6, 5 => -3, 7 => 2, 8 => -2, 15 => -1, 17 => 1, 35 => 2, 47 => 1, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m2_2p1_3p6_6m3_8p2_9m2_16m1_18p1_36p2_48p1_72m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m2_2p1_3p6_6m3_8p2_9m2_16m1_18p1_36p2_48p1_72m1 =
    [0, 0, 1, 2, 4, 2, 2, 0, 4, 4, 2, 0, -4, 4, 2, 8, 0, 0, 2, 0,
     4, -4, 4, 0, 0, 0, 0, 6, 0, 2, -4, 0, 0, 4, -2, 0, 4, 0, -2, -12,
     0, -4, 0, 0, -8, -4, -8, 0, 0, -8, -3, -20, -8, -2, 2, 0, -16, -4, -6, 0,
     8, -8, -2, -12, 0, -4, -8, 0, -4, 0, 0, 0, 0, 0, -2, -2, -16, -4, -4, 0,
     0, -8, 6, 0, 0, 4, -6, 16, 0, 4, -4, 0, 16, 4, 0, 0, 0, 16, 1, 12] := by
  eta_coeff

end WeightTwoCusps
