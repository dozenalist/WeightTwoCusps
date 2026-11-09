module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-1) η(54z)^2 η(81z) η(162z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-1) η(54z)^2 η(81z) η(162z)^(-1)` at level 486. -/
abbrev cuspForm_486_eta_1m2_2p1_3p6_6m2_9m1_54p2_81p1_162m1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -1, 53 => 2, 80 => 1, 161 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m2_2p1_3p6_6m2_9m1_54p2_81p1_162m1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m2_2p1_3p6_6m2_9m1_54p2_81p1_162m1 =
    [0, 1, 2, 4, 2, 2, 0, 3, 2, 0, 1, 0, 4, -1, 0, 0, -1, 2, 0, 0,
     -2, -4, 3, 0, 0, 0, -2, 0, -1, 0, 0, -5, 0, 0, -5, -2, 0, 1, 0, -4,
     2, -4, 0, 4, -2, 0, -3, 2, -8, -5, 0, 0, -2, -2, 0, -5, -6, -4, 0, -6,
     0, -5, -4, 0, -5, -2, -12, -2, 2, 0, -4, -4, 0, 5, 2, 4, -4, 0, 0, 5,
     6, 0, 4, -4, -4, 3, -4, 0, 2, 2, 0, -6, 2, 8, 4, 10, 0, -4, 2, 0] := by
  eta_coeff

end WeightTwoCusps
