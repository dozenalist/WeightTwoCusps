module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-2) η(2z) η(3z)^8 η(6z)^(-4) η(9z)^(-3) η(18z)^2 η(27z)^2 η(81z)^(-1) η(162z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^8 η(6z)^(-4) η(9z)^(-3) η(18z)^2 η(27z)^2 η(81z)^(-1) η(162z)` at level 486. -/
abbrev cuspForm_486_eta_1m2_2p1_3p8_6m4_9m3_18p2_27p2_81m1_162p1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 0 => -2, 1 => 1, 2 => 8, 5 => -4, 8 => -3, 17 => 2, 26 => 2, 80 => -1, 161 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_1m2_2p1_3p8_6m4_9m3_18p2_27p2_81m1_162p1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_1m2_2p1_3p8_6m4_9m3_18p2_27p2_81m1_162p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 4, 0, -2, -8, 0, 0, 4, -3, -2, 4, 0, 2,
     -8, 0, -2, -4, 1, -2, 12, 0, 2, -8, 0, 4, 4, 0, -4, 0, 0, 4, 4, 0,
     0, 0, 8, 4, 0, 0, -4, -4, 0, 2, 8, -3, 6, -4, 0, -4, 0, 0, -8, -4,
     -9, -2, -4, 0, 0, 12, 0, -2, -20, 0, 2, -8, 0, -6, 20, 0, 8, 8, -1, 0,
     -28, 0, -2, 20, 0, -6, -4, 9, 8, 4, 0, -2, -12, 0, 6, 12, -11, -6, 4, 0] := by
  eta_coeff

end WeightTwoCusps
