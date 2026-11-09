module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(4z)^2 η(6z)^(-2) η(8z)^(-1) η(9z)^(-1) η(12z)^(-1) η(24z) η(36z)^2 η(54z) η(72z)^(-1) η(108z)^(-1) η(216z)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(4z)^2 η(6z)^(-2) η(8z)^(-1) η(9z)^(-1) η(12z)^(-1) η(24z) η(36z)^2 η(54z) η(72z)^(-1) η(108z)^(-1) η(216z)` at level 216. -/
abbrev cuspForm_216_eta_1m2_2p1_3p5_4p2_6m2_8m1_9m1_12m1_24p1_36p2_54p1_72m1_108m1_216p1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -2, 1 => 1, 2 => 5, 3 => 2, 5 => -2, 7 => -1, 8 => -1, 11 => -1, 23 => 1, 35 => 2, 53 => 1, 71 => -1, 107 => -1, 215 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m2_2p1_3p5_4p2_6m2_8m1_9m1_12m1_24p1_36p2_54p1_72m1_108m1_216p1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m2_2p1_3p5_4p2_6m2_8m1_9m1_12m1_24p1_36p2_54p1_72m1_108m1_216p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 3, 2, 0, -1, 2, 0, 3, -2, 0, 2,
     0, 4, -3, 2, 0, -1, 2, -4, 0, 0, 0, 1, -4, 0, 0, -2, 0, -1, -4, -4,
     -3, 0, 0, -2, 0, -8, -6, -2, 0, 0, -6, 0, -9, -2, 0, -5, -2, -12, 6, -2,
     0, 1, -6, 0, -3, 2, 0, -2, 0, 0, -3, 0, 0, 0, 2, 4, 9, 0, 0, 2,
     0, 4, -6, 0, 0, 4, 12, 0, 3, 6, 0, 4, 0, 12, 6, -2, 0, 2, 8, 16] := by
  eta_coeff

end WeightTwoCusps
