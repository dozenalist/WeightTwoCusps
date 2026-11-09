module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(8z)^(-1) η(12z)^(-1) η(19z) η(24z)^2 η(38z)^(-1) η(57z)^(-1) η(114z)^2 η(152z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(8z)^(-1) η(12z)^(-1) η(19z) η(24z)^2 η(38z)^(-1) η(57z)^(-1) η(114z)^2 η(152z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_4m1_8m1_12m1_19p1_24p2_38m1_57m1_114p2_152p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 3 => -1, 7 => -1, 11 => -1, 18 => 1, 23 => 2, 37 => -1, 56 => -1, 113 => 2, 151 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_4m1_8m1_12m1_19p1_24p2_38m1_57m1_114p2_152p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_4m1_8m1_12m1_19p1_24p2_38m1_57m1_114p2_152p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, -2,
     0, 0, -2, 2, 0, 0, 0, -2, 0, 0, 2, 0, 0, -1, -5, -2, 0, -1, 0, 2,
     0, 2, -2, -4, 0, 0, 3, 2, 0, -2, 2, 0, 0, 3, 0, 2, 0, 2, -2, -2,
     0, 0, 6, 2, 0, -1, -2, -2, 0, -2, -2, 2, 0, 2, -2, 0, 0, 0, 5, 2,
     0, -2, 0, -2, 0, 0, 2, 2, 0, 2, -2, 0, 0, 0, 2, 4, 0, -3, -5, -4] := by
  eta_coeff

end WeightTwoCusps
