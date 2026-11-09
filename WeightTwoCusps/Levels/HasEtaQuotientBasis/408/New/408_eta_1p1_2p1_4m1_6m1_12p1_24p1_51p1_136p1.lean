module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z) η(2z) η(4z)^(-1) η(6z)^(-1) η(12z) η(24z) η(51z) η(136z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(4z)^(-1) η(6z)^(-1) η(12z) η(24z) η(51z) η(136z)` at level 408. -/
abbrev cuspForm_408_eta_1p1_2p1_4m1_6m1_12p1_24p1_51p1_136p1 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 0 => 1, 1 => 1, 3 => -1, 5 => -1, 11 => 1, 23 => 1, 50 => 1, 135 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_1p1_2p1_4m1_6m1_12p1_24p1_51p1_136p1_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_1p1_2p1_4m1_6m1_12p1_24p1_51p1_136p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 1, 1, 1, 0, 0, 0, -1, -1,
     1, 1, -1, -1, -1, 2, 0, -1, 0, 0, 0, 1, 2, 0, 0, 0, -1, 0, 0, -1,
     -1, 0, -1, 0, 1, 0, 1, -1, 1, 0, 1, 0, 0, 0, -1, -1, 0, 0, 0, 1,
     -2, 2, 1, 0, -1, -2, 2, 2, 0, 1, 0, -1, -1, 0, 1, 1, -3, -1, 1, -1,
     -1, 0, -1, -2, 0, 0, 0, 2, 1, 1, 2, 1, 0, 1, 0, -1, 1, -2, 1, 1] := by
  eta_coeff

end WeightTwoCusps
