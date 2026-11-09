module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z)^(-1) η(4z)^(-2) η(6z)^3 η(12z)^(-1) η(19z)^2 η(38z)^(-1) η(57z)^(-1) η(114z) η(228z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z)^(-1) η(4z)^(-2) η(6z)^3 η(12z)^(-1) η(19z)^2 η(38z)^(-1) η(57z)^(-1) η(114z) η(228z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3m1_4m2_6p3_12m1_19p2_38m1_57m1_114p1_228p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => -1, 3 => -2, 5 => 3, 11 => -1, 18 => 2, 37 => -1, 56 => -1, 113 => 1, 227 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3m1_4m2_6p3_12m1_19p2_38m1_57m1_114p1_228p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3m1_4m2_6p3_12m1_19p2_38m1_57m1_114p1_228p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 4, 0, -1, 0,
     0, 2, -2, 0, 2, 0, 0, -3, 0, 0, 0, -2, -4, -1, -6, -8, -2, 2, 0, 0,
     -2, 4, -2, -8, 0, 0, 6, 0, 1, -4, 0, 2, -2, 8, -2, 4, 0, -1, 0, -4,
     0, 8, 8, -2, 0, 0, 2, -4, 8, -1, -2, 8, 1, 8, 0, -1, 2, 0, 3, 2,
     -8, 2, 4, 0, -5, -4, 4, 2, 4, 0, 0, -4, 0, 2, 4, 0, 2, -4, -8, -2] := by
  eta_coeff

end WeightTwoCusps
