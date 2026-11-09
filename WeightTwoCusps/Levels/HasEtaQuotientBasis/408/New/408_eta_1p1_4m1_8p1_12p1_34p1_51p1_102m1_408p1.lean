module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z) η(4z)^(-1) η(8z) η(12z) η(34z) η(51z) η(102z)^(-1) η(408z)`; see
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

/-- The cuspidal eta quotient `η(z) η(4z)^(-1) η(8z) η(12z) η(34z) η(51z) η(102z)^(-1) η(408z)` at level 408. -/
abbrev cuspForm_408_eta_1p1_4m1_8p1_12p1_34p1_51p1_102m1_408p1 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 0 => 1, 3 => -1, 7 => 1, 11 => 1, 33 => 1, 50 => 1, 101 => -1, 407 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_1p1_4m1_8p1_12p1_34p1_51p1_102m1_408p1_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_1p1_4m1_8p1_12p1_34p1_51p1_102m1_408p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1,
     0, 1, 0, -1, 1, 1, 0, -1, 1, 0, 0, -1, 0, 0, 0, -1, 0, 1, -1, -1,
     0, 0, 1, 1, 1, 1, -1, 0, 0, 0, 0, -1, 0, 2, 0, -1, 0, 1, -2, -1,
     -1, 1, -1, 0, 0, 1, 0, 0, 0, 1, 1, 0, -1, 1, 1, -1, -2, -1, 0, -2,
     1, 1, 2, 1, 1, -2, 4, 0, 0, -1, 1, 0, -2, -3, 1, 0, -2, 0, -1, 2] := by
  eta_coeff

end WeightTwoCusps
