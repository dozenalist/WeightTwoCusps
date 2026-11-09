module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z)^(-2) η(4z)^4 η(6z) η(12z)^(-2) η(24z) η(102z) η(204z)^2 η(408z)^(-1)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(6z) η(12z)^(-2) η(24z) η(102z) η(204z)^2 η(408z)^(-1)` at level 408. -/
abbrev cuspForm_408_eta_2m2_4p4_6p1_12m2_24p1_102p1_204p2_408m1 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 1 => -2, 3 => 4, 5 => 1, 11 => -2, 23 => 1, 101 => 1, 203 => 2, 407 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_2m2_4p4_6p1_12m2_24p1_102p1_204p2_408m1_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_2m2_4p4_6p1_12m2_24p1_102p1_204p2_408m1 =
    [0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0, -1, 0, 2, 0, 2,
     0, 1, 0, -1, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, -2, 0, -1,
     0, 1, 0, 0, 0, 1, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 0, 1, 0, -2,
     0, -2, 0, 0, 0, -3, 0, 2, 0, 0, 0, -2, 0, -2, 0, -1, 0, 2, 0, 0,
     0, 1, 0, 0, 0, -4, 0, -1, 0, 2, 0, 2, 0, 0, 0, -3, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
