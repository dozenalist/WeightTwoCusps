module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^(-1) η(4z)^(-2) η(6z) η(9z)^4 η(18z)^(-3) η(27z)^(-2) η(36z) η(54z)^3 η(108z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^(-1) η(4z)^(-2) η(6z) η(9z)^4 η(18z)^(-3) η(27z)^(-2) η(36z) η(54z)^3 η(108z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m3_2p7_3m1_4m2_6p1_9p4_18m3_27m2_36p1_54p3_108m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -3, 1 => 7, 2 => -1, 3 => -2, 5 => 1, 8 => 4, 17 => -3, 26 => -2, 35 => 1, 53 => 3, 107 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p7_3m1_4m2_6p1_9p4_18m3_27m2_36p1_54p3_108m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p7_3m1_4m2_6p1_9p4_18m3_27m2_36p1_54p3_108m1 =
    [0, 1, 3, 2, 2, 7, 4, 3, 11, 4, 2, 7, 0, 1, -5, -4, 2, -10, 0, -1,
     -9, 0, -2, 10, 0, -7, 10, -4, -2, 0, 0, 2, -13, 8, 0, -21, 0, 3, 4, -4,
     -6, 0, -16, 4, 9, -8, -4, -18, 0, -4, -24, 4, -8, -11, 0, -14, -11, -8, 4, 4,
     0, -5, -21, 0, 2, 4, 0, -13, 0, -16, -2, 8, 0, 7, -8, -2, 4, -15, 8, 7,
     -9, 4, -4, 11, 0, 8, 42, 12, 6, 24, 0, 9, 18, 16, 4, -10, 0, -1, 28, 16] := by
  eta_coeff

end WeightTwoCusps
