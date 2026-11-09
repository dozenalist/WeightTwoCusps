module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(3z) η(6z)^(-1) η(9z)^(-1) η(18z)^2 η(54z) η(81z) η(243z)^(-1) η(486z)^2`; see
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

/-- The cuspidal eta quotient `η(3z) η(6z)^(-1) η(9z)^(-1) η(18z)^2 η(54z) η(81z) η(243z)^(-1) η(486z)^2` at level 486. -/
abbrev cuspForm_486_eta_3p1_6m1_9m1_18p2_54p1_81p1_243m1_486p2 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 2 => 1, 5 => -1, 8 => -1, 17 => 2, 53 => 1, 80 => 1, 242 => -1, 485 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_3p1_6m1_9m1_18p2_54p1_81p1_243m1_486p2_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_3p1_6m1_9m1_18p2_54p1_81p1_243m1_486p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
