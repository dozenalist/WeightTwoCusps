module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(6z)^(-2) η(9z)^(-1) η(18z) η(27z)^2 η(81z)^(-1) η(162z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(6z)^(-2) η(9z)^(-1) η(18z) η(27z)^2 η(81z)^(-1) η(162z)` at level 486. -/
abbrev cuspForm_486_eta_1m2_2p4_3p2_6m2_9m1_18p1_27p2_81m1_162p1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 8 => -1, 17 => 1, 26 => 2, 80 => -1, 161 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m2_2p4_3p2_6m2_9m1_18p1_27p2_81m1_162p1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m2_2p4_3p2_6m2_9m1_18p1_27p2_81m1_162p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, -2, -2, 0, 0, 1, -3, -2, 1, 0, 2,
     -2, 0, -2, -1, 1, -2, 3, 0, 2, -2, 0, 4, 1, 0, -4, 0, 0, 4, 1, 0,
     0, 0, 8, 4, 0, 0, -4, -1, 0, 2, 2, -3, 6, -1, 0, -4, 0, 0, -8, -1,
     -9, -2, -1, 0, 0, 3, 0, -2, -5, 0, 2, -2, 0, -6, 5, 0, 8, 2, -1, 0,
     -7, 0, -2, 5, 0, -6, -1, 9, 8, 1, 0, -2, -3, 0, 6, 3, -11, -6, 1, 0] := by
  eta_coeff

end WeightTwoCusps
