module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(19z)^(-1) η(24z) η(38z)^2 η(57z) η(114z)^(-1) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(19z)^(-1) η(24z) η(38z)^2 η(57z) η(114z)^(-1) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_4m2_19m1_24p1_38p2_57p1_114m1_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 3 => -2, 18 => -1, 23 => 1, 37 => 2, 56 => 1, 113 => -1, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_4m2_19m1_24p1_38p2_57p1_114m1_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_4m2_19m1_24p1_38p2_57p1_114m1_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1,
     2, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 2, 2, 0, 0, 0,
     -2, 0, 0, -1, 0, 0, 0, -2, -1, -2, 0, 0, -4, 0, 0, 2, 0, -2, 0, -2,
     -2, 0, 0, 0, 0, 0, 0, -1, -2, 0, 0, -2, 0, -4, 0, 0, -3, -2, 0, -2] := by
  eta_coeff

end WeightTwoCusps
