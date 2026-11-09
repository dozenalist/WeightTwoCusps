module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(6z)^(-2) η(8z)^(-1) η(24z) η(57z)^(-1) η(114z) η(228z)^4 η(456z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(6z)^(-2) η(8z)^(-1) η(24z) η(57z)^(-1) η(114z) η(228z)^4 η(456z)^(-2)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3p1_6m2_8m1_24p1_57m1_114p1_228p4_456m2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => 1, 5 => -2, 7 => -1, 23 => 1, 56 => -1, 113 => 1, 227 => 4, 455 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3p1_6m2_8m1_24p1_57m1_114p1_228p4_456m2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3p1_6m2_8m1_24p1_57m1_114p1_228p4_456m2 =
    [0, 0, 0, 1, 2, 0, -1, -2, -4, 1, 2, 0, 0, -4, 0, 1, 2, 4, -2, 0,
     0, 1, 2, 0, -1, -2, 0, 1, 4, 0, -2, -2, 0, 1, 0, 4, -1, -2, 0, 1,
     0, 0, -1, -6, -4, 0, 2, 0, -2, -2, 0, 1, 2, 4, 0, -2, 0, 0, 4, 0,
     0, 2, -4, 1, 2, -4, 0, 2, 0, 2, -2, 4, 0, -2, 4, -2, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 2, 0, -1, 2, 0, 0, -2, 4, 2, 0, 0, 1, -2, -8, 0] := by
  eta_coeff

end WeightTwoCusps
