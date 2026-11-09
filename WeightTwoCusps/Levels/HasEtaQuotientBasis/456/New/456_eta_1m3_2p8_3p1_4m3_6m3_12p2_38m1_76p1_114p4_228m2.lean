module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(38z)^(-1) η(76z) η(114z)^4 η(228z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(38z)^(-1) η(76z) η(114z)^4 η(228z)^(-2)` at level 456. -/
abbrev cuspForm_456_eta_1m3_2p8_3p1_4m3_6m3_12p2_38m1_76p1_114p4_228m2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 37 => -1, 75 => 1, 113 => 4, 227 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m3_2p8_3p1_4m3_6m3_12p2_38m1_76p1_114p4_228m2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m3_2p8_3p1_4m3_6m3_12p2_38m1_76p1_114p4_228m2 =
    [0, 0, 1, 3, 1, -3, -1, 0, 0, 3, -1, -3, -2, -3, 1, 0, -1, 0, -1, 0,
     0, 3, 1, -3, 1, 3, -1, 0, 1, 0, 0, -3, 2, 0, 1, 3, 0, 3, 0, 3,
     0, 3, 3, -3, 0, -3, 0, 3, -2, -6, -2, -6, 0, 3, -1, 3, -2, 0, 1, 3,
     2, -3, -2, 3, -1, -3, 0, 0, -1, -6, 1, 3, 2, 0, 0, 0, 0, 3, 0, 6,
     2, -6, -2, 0, 0, 3, -1, -9, -2, -3, 1, 3, -1, 6, -1, 0, 1, 3, 2, -3] := by
  eta_coeff

end WeightTwoCusps
