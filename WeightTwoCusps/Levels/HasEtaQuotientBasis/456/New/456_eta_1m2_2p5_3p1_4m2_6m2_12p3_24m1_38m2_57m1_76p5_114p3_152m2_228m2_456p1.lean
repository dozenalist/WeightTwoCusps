module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z)^3 η(24z)^(-1) η(38z)^(-2) η(57z)^(-1) η(76z)^5 η(114z)^3 η(152z)^(-2) η(228z)^(-2) η(456z)`; see
[the local level table](../../TABLE.md#level-456).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z)^3 η(24z)^(-1) η(38z)^(-2) η(57z)^(-1) η(76z)^5 η(114z)^3 η(152z)^(-2) η(228z)^(-2) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_12p3_24m1_38m2_57m1_76p5_114p3_152m2_228m2_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 11 => 3, 23 => -1, 37 => -2, 56 => -1, 75 => 5, 113 => 3, 151 => -2, 227 => -2, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_12p3_24m1_38m2_57m1_76p5_114p3_152m2_228m2_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3p1_4m2_6m2_12p3_24m1_38m2_57m1_76p5_114p3_152m2_228m2_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, -1, 0, 0, 1, 0,
     0, 0, -2, 0, -2, -4, 0, 1, 0, 0, -2, 0, 0, -1, 4, 0, 0, 0, 0, 2,
     -2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 4, 4, -2, 0, 0, 2, -1, 0, 0,
     -4, 4, -4, -10, 0, 2, 2, 2, -4, 3, -2, -2, 7, 0, 0, -1, 0, 4, -3, -6,
     0, -4, -4, 4, 1, 0, 2, -2, -4, 0, 6, 4, 0, 0, 0, -2, 4, -2, 0, 8] := by
  eta_coeff

end WeightTwoCusps
