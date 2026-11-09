module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z)^(-1) η(9z)^2 η(27z)^(-2) η(54z)^3 η(108z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z)^(-1) η(9z)^2 η(27z)^(-2) η(54z)^3 η(108z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m2_2p3_3p2_4m1_9p2_27m2_54p3_108m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 8 => 2, 26 => -2, 53 => 3, 107 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m2_2p3_3p2_4m1_9p2_27m2_54p3_108m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m2_2p3_3p2_4m1_9p2_27m2_54p3_108m1 =
    [0, 1, 2, 2, 2, 2, 4, 3, 2, 4, 2, 2, 0, 1, 2, -4, 2, 4, 0, -1,
     -6, 0, -2, -4, 0, -7, -4, -4, -2, 0, 0, 2, 2, 8, 0, -6, 0, 3, 8, -4,
     -6, 0, -16, 4, 6, -8, -4, -12, 0, -4, -16, 4, -8, -10, 0, -14, -2, -8, 4, 8,
     0, -5, -14, 0, 2, 8, 0, -13, 0, -16, -2, 16, 0, 7, -16, -2, 4, -18, 8, 7,
     -6, 4, -4, 10, 0, 8, 28, 12, 6, 0, 0, 9, 12, 16, 4, 4, 0, -1, 40, 16] := by
  eta_coeff

end WeightTwoCusps
