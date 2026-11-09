module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-2) η(8z)^(-1) η(9z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(36z) η(48z)^(-1) η(96z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-2) η(8z)^(-1) η(9z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(36z) η(48z)^(-1) η(96z)` at level 288. -/
abbrev cuspForm_288_eta_1m2_2p2_3p5_6m2_8m1_9m1_16p2_24p1_32m1_36p1_48m1_96p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 2, 2 => 5, 5 => -2, 7 => -1, 8 => -1, 15 => 2, 23 => 1, 31 => -1, 35 => 1, 47 => -1, 95 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m2_2p2_3p5_6m2_8m1_9m1_16p2_24p1_32m1_36p1_48m1_96p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m2_2p2_3p5_6m2_8m1_9m1_16p2_24p1_32m1_36p1_48m1_96p1 =
    [0, 0, 0, 0, 1, 2, 3, 1, -1, -1, -1, 1, -2, 1, 1, 0, 0, -5, -1, -3,
     -1, 0, -6, -2, 0, -1, 1, -4, 4, 0, -6, 3, 0, 4, 1, 0, 2, -4, 1, 8,
     0, 3, 0, -1, 2, 2, 12, 0, 0, 4, -1, 0, -6, 8, 3, -2, 4, -4, 3, 1,
     4, 4, -5, 0, 0, -4, 4, 3, 1, -8, 0, 2, 0, -5, -4, 0, -16, -12, -6, -1,
     0, -1, -3, -1, 0, 1, -5, -16, 0, 9, 2, 2, -4, 8, 0, 2, 0, 3, 4, 4] := by
  eta_coeff

end WeightTwoCusps
