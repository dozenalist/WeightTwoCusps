module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(3z) η(4z)^4 η(8z)^(-2) η(12z)^(-2) η(19z) η(24z)^2 η(57z)^(-1) η(114z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(4z)^4 η(8z)^(-2) η(12z)^(-2) η(19z) η(24z)^2 η(57z)^(-1) η(114z)^2` at level 456. -/
abbrev cuspForm_456_eta_1m1_3p1_4p4_8m2_12m2_19p1_24p2_57m1_114p2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 2 => 1, 3 => 4, 7 => -2, 11 => -2, 18 => 1, 23 => 2, 56 => -1, 113 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_3p1_4p4_8m2_12m2_19p1_24p2_57m1_114p2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_3p1_4p4_8m2_12m2_19p1_24p2_57m1_114p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 1, -1, 1, 1, 0, 2,
     -1, 2, 2, 1, 2, 1, 2, 1, 0, -1, -3, -1, 1, 1, 1, 0, 0, 0, 0, 1,
     -2, -2, 0, -1, 1, -1, 0, 0, 1, 0, -2, -1, -3, 2, 0, -1, 0, -2, 3, -2,
     -1, 1, -3, -1, -3, -3, -3, 0, 4, 1, -2, 0, -2, -2, 1, 0, 0, -2, 3, 3,
     -2, 1, -1, 2, 1, -1, -2, -4, -1, 4, 1, 0, -1, -1, 1, -4, 0, -1, -5, -3] := by
  eta_coeff

end WeightTwoCusps
