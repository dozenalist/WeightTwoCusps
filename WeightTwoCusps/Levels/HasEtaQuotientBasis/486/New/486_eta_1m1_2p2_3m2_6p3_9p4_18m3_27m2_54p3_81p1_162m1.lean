module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-1) η(2z)^2 η(3z)^(-2) η(6z)^3 η(9z)^4 η(18z)^(-3) η(27z)^(-2) η(54z)^3 η(81z) η(162z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z)^(-2) η(6z)^3 η(9z)^4 η(18z)^(-3) η(27z)^(-2) η(54z)^3 η(81z) η(162z)^(-1)` at level 486. -/
abbrev cuspForm_486_eta_1m1_2p2_3m2_6p3_9p4_18m3_27m2_54p3_81p1_162m1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -1, 1 => 2, 2 => -2, 5 => 3, 8 => 4, 17 => -3, 26 => -2, 53 => 3, 80 => 1, 161 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m1_2p2_3m2_6p3_9p4_18m3_27m2_54p3_81p1_162m1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m1_2p2_3m2_6p3_9p4_18m3_27m2_54p3_81p1_162m1 =
    [0, 1, 1, 0, 3, 2, 0, 5, 2, 0, 4, 1, 0, -1, -1, 0, -4, 0, 0, -4,
     -1, 0, 2, -1, 0, 4, -1, 0, 0, -2, 0, -4, 3, 0, -9, 1, 0, 2, 2, 0,
     4, -4, 0, 5, -5, 0, -2, 1, 0, -12, -2, 0, -3, 0, 0, -12, -8, 0, -1, -1,
     0, -7, -1, 0, -5, 1, 0, 2, 0, 0, -7, -6, 0, 8, 2, 0, -6, -1, 0, 8,
     5, 0, 7, -5, 0, 0, -1, 0, 2, 3, 0, -14, 5, 0, 5, 4, 0, -1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
