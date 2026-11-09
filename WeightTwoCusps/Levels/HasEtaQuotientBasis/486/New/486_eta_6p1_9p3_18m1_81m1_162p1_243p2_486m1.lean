module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(6z) η(9z)^3 η(18z)^(-1) η(81z)^(-1) η(162z) η(243z)^2 η(486z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(6z) η(9z)^3 η(18z)^(-1) η(81z)^(-1) η(162z) η(243z)^2 η(486z)^(-1)` at level 486. -/
abbrev cuspForm_486_eta_6p1_9p3_18m1_81m1_162p1_243p2_486m1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 5 => 1, 8 => 3, 17 => -1, 80 => -1, 161 => 1, 242 => 2, 485 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_6p1_9p3_18m1_81m1_162p1_243p2_486m1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_6p1_9p3_18m1_81m1_162p1_243p2_486m1 =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -3, 0, 0, -1, 0, 0, 3,
     0, 0, 1, 0, 0, 3, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0,
     2, 0, 0, -5, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -2, 0, 0, -4, 0,
     0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 6, 0, 0, 1, 0, 0, -3, 0, 0, -2,
     0, 0, 4, 0, 0, 4, 0, 0, -2, 0, 0, -2, 0, 0, -3, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
