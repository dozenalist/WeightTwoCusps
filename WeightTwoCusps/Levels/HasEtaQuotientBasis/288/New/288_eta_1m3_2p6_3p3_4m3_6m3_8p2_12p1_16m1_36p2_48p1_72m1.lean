module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-3) η(6z)^(-3) η(8z)^2 η(12z) η(16z)^(-1) η(36z)^2 η(48z) η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-3) η(6z)^(-3) η(8z)^2 η(12z) η(16z)^(-1) η(36z)^2 η(48z) η(72z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m3_2p6_3p3_4m3_6m3_8p2_12p1_16m1_36p2_48p1_72m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 6, 2 => 3, 3 => -3, 5 => -3, 7 => 2, 11 => 1, 15 => -1, 35 => 2, 47 => 1, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m3_2p6_3p3_4m3_6m3_8p2_12p1_16m1_36p2_48p1_72m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m3_2p6_3p3_4m3_6m3_8p2_12p1_16m1_36p2_48p1_72m1 =
    [0, 0, 1, 3, 3, 1, 0, 3, 6, 3, 1, 0, 0, 1, 2, 6, 0, -3, 0, 3,
     6, 0, 2, 0, 0, 3, 0, 3, 0, 1, 0, -3, 0, 0, -1, 0, 0, 0, -2, -6,
     0, 1, 0, -3, -12, -6, -4, 0, 0, -8, -3, -18, -6, 5, 0, -6, -24, 0, -3, 0,
     0, -8, -2, -12, 0, -2, 0, -3, -6, 0, 0, 0, 0, 3, -2, -3, -12, -8, 0, -3,
     0, -9, 3, 0, 0, 13, -6, 6, 0, 5, 0, -6, 24, 0, 0, 0, 0, 7, 1, 12] := by
  eta_coeff

end WeightTwoCusps
