module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(8z) η(12z)^3 η(19z)^2 η(24z)^(-1) η(38z)^(-2) η(57z)^(-2) η(114z)^3 η(152z) η(228z) η(456z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(8z) η(12z)^3 η(19z)^2 η(24z)^(-1) η(38z)^(-2) η(57z)^(-2) η(114z)^3 η(152z) η(228z) η(456z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p4_3p2_4m2_6m3_8p1_12p3_19p2_24m1_38m2_57m2_114p3_152p1_228p1_456m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -3, 7 => 1, 11 => 3, 18 => 2, 23 => -1, 37 => -2, 56 => -2, 113 => 3, 151 => 1, 227 => 1, 455 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p4_3p2_4m2_6m3_8p1_12p3_19p2_24m1_38m2_57m2_114p3_152p1_228p1_456m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p4_3p2_4m2_6m3_8p1_12p3_19p2_24m1_38m2_57m2_114p3_152p1_228p1_456m1 =
    [0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 3, 2, 2, 0, 0, 2, 3, 2, 0,
     0, 0, 0, 2, 2, -3, -2, 0, 2, -2, -4, 0, -4, 0, 0, -1, -2, -4, 0, 0,
     0, 4, -2, -7, 0, 1, 4, -3, 0, 1, -6, 2, 2, 2, -2, -5, 2, 0, 0, 4,
     -8, 1, 4, 1, 2, -6, 6, 0, -2, 4, 2, 0, -2, -1, 4, 0, 0, 1, -6, 6,
     -4, 0, 2, -2, 2, -9, -2, 2, 0, -2, -2, -2, 2, 0, 0, 1, 2, 0, -4, 3] := by
  eta_coeff

end WeightTwoCusps
