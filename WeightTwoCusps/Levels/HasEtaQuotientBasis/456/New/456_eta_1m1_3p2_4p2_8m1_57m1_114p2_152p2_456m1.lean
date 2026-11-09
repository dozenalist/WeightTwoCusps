module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(3z)^2 η(4z)^2 η(8z)^(-1) η(57z)^(-1) η(114z)^2 η(152z)^2 η(456z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z)^2 η(8z)^(-1) η(57z)^(-1) η(114z)^2 η(152z)^2 η(456z)^(-1)` at level 456. -/
abbrev cuspForm_456_eta_1m1_3p2_4p2_8m1_57m1_114p2_152p2_456m1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 2 => 2, 3 => 2, 7 => -1, 56 => -1, 113 => 2, 151 => 2, 455 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_3p2_4p2_8m1_57m1_114p2_152p2_456m1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_3p2_4p2_8m1_57m1_114p2_152p2_456m1 =
    [0, 1, 1, 2, 1, 1, 1, 0, 2, 0, 1, 1, 1, 1, -1, -1, 1, 0, 2, 1,
     -2, 0, 0, 1, 0, -1, 1, 0, -2, 1, -3, -1, 1, 2, 0, -1, 0, -1, 0, -2,
     0, -2, -1, 3, -2, 0, -1, -2, 0, -2, 0, 1, 0, -1, -1, -2, 1, -1, 2, 1,
     1, 1, -1, -2, -1, 1, 1, 1, 2, 0, -2, -1, -2, 2, 1, 3, -1, -2, 0, -4,
     0, 0, 1, 2, -1, -3, -1, -4, 1, 1, 2, 1, -4, 0, -3, -2, -2, 0, -2, 2] := by
  eta_coeff

end WeightTwoCusps
