module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-1) η(8z)^(-1) η(9z)^(-2) η(16z)^2 η(18z)^3 η(24z) η(32z)^(-1) η(36z)^(-1) η(48z)^(-1) η(96z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-1) η(8z)^(-1) η(9z)^(-2) η(16z)^2 η(18z)^3 η(24z) η(32z)^(-1) η(36z)^(-1) η(48z)^(-1) η(96z)` at level 288. -/
abbrev cuspForm_288_eta_1m2_2p2_3p4_6m1_8m1_9m2_16p2_18p3_24p1_32m1_36m1_48m1_96p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 2, 2 => 4, 5 => -1, 7 => -1, 8 => -2, 15 => 2, 17 => 3, 23 => 1, 31 => -1, 35 => -1, 47 => -1, 95 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m2_2p2_3p4_6m1_8m1_9m2_16p2_18p3_24p1_32m1_36m1_48m1_96p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m2_2p2_3p4_6m1_8m1_9m2_16p2_18p3_24p1_32m1_36m1_48m1_96p1 =
    [0, 0, 0, 1, 2, 3, 2, 1, 2, 1, 2, 0, 4, 7, 6, 6, 0, 3, 2, 3,
     2, 0, 4, 4, 0, -3, -2, 1, 0, -5, -4, -5, 0, -4, -2, -4, -4, -4, -10, -2,
     0, -1, 0, -3, -4, -2, -8, 4, 0, 0, 2, -14, -4, -1, 2, 2, -8, 4, -6, -4,
     -8, -4, 2, -8, 0, -14, -8, 1, -2, 8, 0, -12, 0, -11, 8, -1, -8, 0, -4, 3,
     0, 1, 6, 8, 0, -9, -14, -2, 0, 11, -4, -2, 8, -8, 0, -8, 0, 17, -8, 12] := by
  eta_coeff

end WeightTwoCusps
