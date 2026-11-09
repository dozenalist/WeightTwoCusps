module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-1) η(3z)^2 η(4z)^2 η(8z)^(-1) η(12z)^(-1) η(19z) η(24z) η(76z)^(-1) η(152z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z)^2 η(8z)^(-1) η(12z)^(-1) η(19z) η(24z) η(76z)^(-1) η(152z)^2` at level 456. -/
abbrev cuspForm_456_eta_1m1_3p2_4p2_8m1_12m1_19p1_24p1_76m1_152p2 : gamma0CuspForms 456 :=
  etaQuotientCuspForm 456 sparse![456; 0 => -1, 2 => 2, 3 => 2, 7 => -1, 11 => -1, 18 => 1, 23 => 1, 75 => -1, 151 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_456_eta_1m1_3p2_4p2_8m1_12m1_19p1_24p1_76m1_152p2_first_coeffs :
    first_coeffs 100 cuspForm_456_eta_1m1_3p2_4p2_8m1_12m1_19p1_24p1_76m1_152p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 1, 1, 0, 2, 0,
     1, 1, 1, 2, 0, 1, 2, 1, 3, 1, -1, -1, -1, 1, 0, 0, 1, -1, 0, 1,
     -1, -1, -1, 2, 0, -1, 0, -2, 1, 0, 0, -2, -3, 1, -1, 1, -2, 0, -1, -1,
     0, -2, 0, -2, -2, 0, -4, -2, 1, 0, -1, -2, -3, -2, -3, -1, 0, -3, 4, 1,
     -2, -3, 0, 0, -1, -1, -3, -2, 1, 1, 2, -1, 2, 0, 1, 0, -1, -2, 0, 2] := by
  eta_coeff

end WeightTwoCusps
