module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-1) η(2z) η(4z) η(6z)^2 η(8z)^(-1) η(9z)^3 η(12z)^(-2) η(18z)^(-2) η(24z)^2 η(27z)^(-2) η(36z)^2 η(54z)^3 η(72z)^(-1) η(108z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z) η(6z)^2 η(8z)^(-1) η(9z)^3 η(12z)^(-2) η(18z)^(-2) η(24z)^2 η(27z)^(-2) η(36z)^2 η(54z)^3 η(72z)^(-1) η(108z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m1_2p1_4p1_6p2_8m1_9p3_12m2_18m2_24p2_27m2_36p2_54p3_72m1_108m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -1, 1 => 1, 3 => 1, 5 => 2, 7 => -1, 8 => 3, 11 => -2, 17 => -2, 23 => 2, 26 => -2, 35 => 2, 53 => 3, 71 => -1, 107 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m1_2p1_4p1_6p2_8m1_9p3_12m2_18m2_24p2_27m2_36p2_54p3_72m1_108m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m1_2p1_4p1_6p2_8m1_9p3_12m2_18m2_24p2_27m2_36p2_54p3_72m1_108m1 =
    [0, 1, 1, 1, 2, 1, 2, 1, 1, 2, -2, 1, 0, -3, 1, -2, 2, 2, 0, 5,
     -3, 0, 2, -2, 0, -3, -2, -2, -2, 0, 0, 2, 1, 4, 0, -3, 0, -5, 4, -2,
     -6, 0, -8, 0, 3, -4, 4, -6, 0, 4, -8, 2, -8, -5, 0, -10, -1, -4, -4, 4,
     0, 3, -7, 0, 2, 4, 0, -7, 0, -8, 2, 8, 0, 3, -8, -1, 4, -9, 4, -3,
     -3, 2, 4, 5, 0, 4, 14, 6, 6, 0, 0, -1, 6, 8, -4, 2, 0, 11, 20, 8] := by
  eta_coeff

end WeightTwoCusps
