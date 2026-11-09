module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z)^(-1) η(19z)^(-1) η(24z)^2 η(38z)^(-1) η(57z)^2 η(76z)^5 η(152z)^(-2) η(228z)^(-2) η(456z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z)^(-1) η(19z)^(-1) η(24z)^2 η(38z)^(-1) η(57z)^2 η(76z)^5 η(152z)^(-2) η(228z)^(-2) η(456z)` at level 456. -/
abbrev cuspForm_456_eta_1m2_2p5_3p1_4m1_6m2_8m1_19m1_24p2_38m1_57p2_76p5_152m2_228m2_456p1 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -1, 5 => -2, 7 => -1, 18 => -1, 23 => 2, 37 => -1, 56 => 2, 75 => 5, 151 => -2, 227 => -2, 455 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m2_2p5_3p1_4m1_6m2_8m1_19m1_24p2_38m1_57p2_76p5_152m2_228m2_456p1_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m2_2p5_3p1_4m1_6m2_8m1_19m1_24p2_38m1_57p2_76p5_152m2_228m2_456p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, -1, -1, -2, 1, 1, 0, 0, -3, 0, 0,
     0, 2, -1, 0, 0, 0, 2, 1, -3, -1, 0, -2, 2, 0, 0, -2, -3, 2, 0, 3,
     4, -1, 0, 1, 0, 5, 5, -4, -2, -4, -6, 4, 1, 0, -3, -7, 3, 0, 3, 8,
     -4, 0, 3, -1, 6, 1, -12, -3, -1, -4, 5, -1, 3, -6, -5, 8, 0, 9, 10, -3,
     0, 3, -3, 7, 1, -10, -2, -6, -4, 3, -2, 2, -9, -2, 11, 0, 6, 7, -3, -2] := by
  eta_coeff

end WeightTwoCusps
