module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(3z) η(4z)^4 η(6z) η(8z)^(-2) η(12z)^(-2) η(19z) η(24z) η(38z)^(-1) η(57z)^(-1) η(114z)^2 η(152z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(4z)^4 η(6z) η(8z)^(-2) η(12z)^(-2) η(19z) η(24z) η(38z)^(-1) η(57z)^(-1) η(114z)^2 η(152z)` at level 456. -/
abbrev cuspForm_456_eta_1m1_3p1_4p4_6p1_8m2_12m2_19p1_24p1_38m1_57m1_114p2_152p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 2 => 1, 3 => 4, 5 => 1, 7 => -2, 11 => -2, 18 => 1, 23 => 1, 37 => -1, 56 => -1, 113 => 2, 151 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_3p1_4p4_6p1_8m2_12m2_19p1_24p1_38m1_57m1_114p2_152p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_3p1_4p4_6p1_8m2_12m2_19p1_24p1_38m1_57m1_114p2_152p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 1, -2,
     0, -1, -2, 2, -2, 2, 0, -2, 0, -1, 2, 0, -3, -3, -5, -4, 0, -1, 0, 2,
     3, 0, -2, -2, -2, 0, 3, 2, -1, -2, 2, 2, 2, 4, 0, 2, 0, 2, -2, -4,
     2, 2, 6, 2, 0, 1, -2, 0, 0, -3, -2, 2, 1, 2, -2, 0, 0, -2, 5, 2,
     0, 0, 0, -2, -2, 0, 2, 2, 3, 2, -2, -2, 0, 0, 2, 4, 2, -3, -5, -6] := by
  eta_coeff

end WeightTwoCusps
