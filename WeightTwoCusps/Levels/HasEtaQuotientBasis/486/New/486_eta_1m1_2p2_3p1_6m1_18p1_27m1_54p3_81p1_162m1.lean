module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(18z) η(27z)^(-1) η(54z)^3 η(81z) η(162z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(18z) η(27z)^(-1) η(54z)^3 η(81z) η(162z)^(-1)` at level 486. -/
abbrev cuspForm_486_eta_1m1_2p2_3p1_6m1_18p1_27m1_54p3_81p1_162m1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 26 => -1, 53 => 3, 80 => 1, 161 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m1_2p2_3p1_6m1_18p1_27m1_54p3_81p1_162m1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m1_2p2_3p1_6m1_18p1_27m1_54p3_81p1_162m1 =
    [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -1,
     0, -1, -1, 0, 0, 1, 0, 0, 1, 0, 3, 1, 0, 0, -1, 0, 0, 1, 0, -1,
     -1, 0, 0, 1, 0, 0, -2, 0, 1, -1, 0, 0, 2, 0, 0, 2, 0, -1, -1, 0,
     0, 1, 0, 0, 0, 0, 3, -2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
     0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, -2, 0, 2, 1, 0, 0, -3, 0, 0] := by
  eta_coeff

end WeightTwoCusps
