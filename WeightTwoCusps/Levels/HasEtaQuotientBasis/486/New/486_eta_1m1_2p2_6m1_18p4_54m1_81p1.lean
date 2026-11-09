module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-1) η(2z)^2 η(6z)^(-1) η(18z)^4 η(54z)^(-1) η(81z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(6z)^(-1) η(18z)^4 η(54z)^(-1) η(81z)` at level 486. -/
abbrev cuspForm_486_eta_1m1_2p2_6m1_18p4_54m1_81p1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -1, 1 => 2, 5 => -1, 17 => 4, 53 => -1, 80 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m1_2p2_6m1_18p4_54m1_81p1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m1_2p2_6m1_18p4_54m1_81p1 =
    [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 1, 0, 1, 1, 0, 3, 2, 0, 3,
     1, 0, 1, -1, 0, 1, 2, 0, 0, 1, 0, 4, 0, 0, 0, -1, 0, 0, 2, 0,
     1, 1, 0, 1, 1, 0, -1, -3, 0, -2, 0, 0, -3, -2, 0, -1, -2, 0, -2, 2,
     0, 1, -3, 0, 3, 2, 0, -5, 2, 0, 1, 2, 0, 0, -2, 0, -1, -4, 0, -2,
     -2, 0, -4, 0, 0, 0, -3, 0, -4, -1, 0, -8, -1, 0, 1, -1, 0, -11, -2, 0] := by
  eta_coeff

end WeightTwoCusps
