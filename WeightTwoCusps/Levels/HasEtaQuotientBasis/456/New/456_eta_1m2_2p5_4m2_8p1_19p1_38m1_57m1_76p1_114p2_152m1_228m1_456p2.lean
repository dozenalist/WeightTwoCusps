module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z) η(19z) η(38z)^(-1) η(57z)^(-1) η(76z) η(114z)^2 η(152z)^(-1) η(228z)^(-1) η(456z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z) η(19z) η(38z)^(-1) η(57z)^(-1) η(76z) η(114z)^2 η(152z)^(-1) η(228z)^(-1) η(456z)^2` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_4m2_8p1_19p1_38m1_57m1_76p1_114p2_152m1_228m1_456p2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 3 => -2, 7 => 1, 18 => 1, 37 => -1, 56 => -1, 75 => 1, 113 => 2, 151 => -1, 227 => -1, 455 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_4m2_8p1_19p1_38m1_57m1_76p1_114p2_152m1_228m1_456p2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_4m2_8p1_19p1_38m1_57m1_76p1_114p2_152m1_228m1_456p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0,
     -1, 0, 0, 0, -2, 0, 0, 0, 1, -4, 0, -1, -4, 0, 0, -2, -2, 0, 0, 1,
     0, 0, 0, 2, -2, -2, 0, -1, 6, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0,
     0, 4, 0, 2, 0, 0, 0, -2, 3, 0, 0, -1, 2, 0, 0, 0, 2, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
