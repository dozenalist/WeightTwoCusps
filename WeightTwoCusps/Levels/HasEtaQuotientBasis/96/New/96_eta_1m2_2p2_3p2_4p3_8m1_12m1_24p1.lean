module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 96

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^2 η(4z)^3 η(8z)^(-1) η(12z)^(-1) η(24z)`; see
[the local level table](../../TABLE.md#level-96).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^2 η(4z)^3 η(8z)^(-1) η(12z)^(-1) η(24z)` at level 96. -/
abbrev cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1 : gamma0CuspForms 96 :=
  etaQuotientCuspForm 96 sparse![96; 0 => -2, 1 => 2, 2 => 2, 3 => 3, 7 => -1, 11 => -1, 23 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1 =
    [0, 1, 2, 3, 4, 2, 2, 0, 0, 1, -4, 0, -4, -2, 0, -6, 0, -6, 2, 0,
     -8, -4, -8, 0, 0, -1, -4, -9, 0, 2, -4, 0, 0, 4, 4, 0, 4, -2, 8, 18,
     0, 2, 0, 0, 16, 2, 16, 0, 0, 9, -2, 6, -8, 10, 2, 0, 0, -4, 12, 0,
     8, 6, -16, 0, 0, -4, -8, 0, 8, 0, 0, 0, 0, -6, 12, -3, -16, -16, -4, 0,
     0, 1, -12, 0, 0, -12, -8, -30, 0, 10, -4, 0, -32, 4, 0, 0, 0, -14, -14, 0] := by
  eta_coeff

end WeightTwoCusps
