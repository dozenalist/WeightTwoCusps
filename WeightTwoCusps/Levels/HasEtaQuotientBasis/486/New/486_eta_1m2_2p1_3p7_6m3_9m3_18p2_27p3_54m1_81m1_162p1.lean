module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-3) η(18z)^2 η(27z)^3 η(54z)^(-1) η(81z)^(-1) η(162z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-3) η(18z)^2 η(27z)^3 η(54z)^(-1) η(81z)^(-1) η(162z)` at level 486. -/
abbrev cuspForm_486_eta_1m2_2p1_3p7_6m3_9m3_18p2_27p3_54m1_81m1_162p1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -3, 17 => 2, 26 => 3, 53 => -1, 80 => -1, 161 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m2_2p1_3p7_6m3_9m3_18p2_27p3_54m1_81m1_162p1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m2_2p1_3p7_6m3_9m3_18p2_27p3_54m1_81m1_162p1 =
    [0, 0, 0, 0, 0, 1, 2, 4, 1, 0, -4, 1, 0, 0, -1, 0, 8, -1, 0, -8,
     0, 0, -4, -1, -4, 8, 0, 0, -8, -2, 0, -4, -3, -6, 4, -4, 0, -4, -4, 0,
     0, 4, -2, -4, 2, 0, 4, 0, 0, 4, 4, 12, 0, 1, 0, 4, 7, 0, 8, -1,
     6, -4, 4, 0, 12, 5, 0, -4, -4, 6, -8, 5, 0, 12, 1, 0, 4, -4, -2, -12,
     -4, 0, 8, -3, 0, 0, 10, -6, -20, 2, 0, 8, -2, 0, 0, -1, 2, 0, -13, 0] := by
  eta_coeff

end WeightTwoCusps
