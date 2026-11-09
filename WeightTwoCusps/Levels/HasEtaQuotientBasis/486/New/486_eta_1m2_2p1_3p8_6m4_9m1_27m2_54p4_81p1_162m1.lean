module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-2) η(2z) η(3z)^8 η(6z)^(-4) η(9z)^(-1) η(27z)^(-2) η(54z)^4 η(81z) η(162z)^(-1)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^8 η(6z)^(-4) η(9z)^(-1) η(27z)^(-2) η(54z)^4 η(81z) η(162z)^(-1)` at level 486. -/
abbrev cuspForm_486_eta_1m2_2p1_3p8_6m4_9m1_27m2_54p4_81p1_162m1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -2, 1 => 1, 2 => 8, 5 => -4, 8 => -1, 26 => -2, 53 => 4, 80 => 1, 161 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m2_2p1_3p8_6m4_9m1_27m2_54p4_81p1_162m1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m2_2p1_3p8_6m4_9m1_27m2_54p4_81p1_162m1 =
    [0, 0, 0, 1, 2, 4, 0, -2, -8, 0, 0, 4, -5, -6, -4, 0, 6, 8, 0, -2,
     -12, 8, 4, 8, 0, -4, 0, 0, 8, 16, -3, 2, -12, 0, -2, -4, 0, -10, -4, -1,
     -2, 4, 0, 2, -4, 0, 2, -12, -5, -2, 4, 0, 4, 28, 0, 4, 4, 8, 4, -16,
     0, -10, -8, 0, 0, 8, 0, 2, -16, 0, 0, -4, 0, -6, -8, -8, 2, 32, 0, 6,
     8, 0, 0, 0, -4, -12, -8, 0, 6, -4, 0, 8, -8, 20, 2, -16, 0, -6, -4, 0] := by
  eta_coeff

end WeightTwoCusps
