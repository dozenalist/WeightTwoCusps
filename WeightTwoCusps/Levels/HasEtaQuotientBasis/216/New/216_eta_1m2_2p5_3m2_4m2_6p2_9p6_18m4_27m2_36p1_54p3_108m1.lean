module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-2) η(2z)^5 η(3z)^(-2) η(4z)^(-2) η(6z)^2 η(9z)^6 η(18z)^(-4) η(27z)^(-2) η(36z) η(54z)^3 η(108z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z)^(-2) η(4z)^(-2) η(6z)^2 η(9z)^6 η(18z)^(-4) η(27z)^(-2) η(36z) η(54z)^3 η(108z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m2_2p5_3m2_4m2_6p2_9p6_18m4_27m2_36p1_54p3_108m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -2, 1 => 5, 2 => -2, 3 => -2, 5 => 2, 8 => 6, 17 => -4, 26 => -2, 35 => 1, 53 => 3, 107 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m2_2p5_3m2_4m2_6p2_9p6_18m4_27m2_36p1_54p3_108m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m2_2p5_3m2_4m2_6p2_9p6_18m4_27m2_36p1_54p3_108m1 =
    [0, 1, 2, 0, 2, 6, 0, 3, 10, 0, 2, 6, 0, 1, -6, 0, 2, -12, 0, -1,
     -6, 0, -2, 12, 0, -7, 12, 0, -2, 0, 0, 2, -14, 0, 0, -18, 0, 3, 0, 0,
     -6, 0, 0, 4, 6, 0, -4, -12, 0, -4, -16, 0, -8, -6, 0, -14, -10, 0, 4, 0,
     0, -5, -14, 0, 2, 0, 0, -13, 0, 0, -2, 0, 0, 7, 0, 0, 4, -6, 0, 7,
     -6, 0, -4, 6, 0, 8, 28, 0, 6, 24, 0, 9, 12, 0, 4, -12, 0, -1, 8, 0] := by
  eta_coeff

end WeightTwoCusps
