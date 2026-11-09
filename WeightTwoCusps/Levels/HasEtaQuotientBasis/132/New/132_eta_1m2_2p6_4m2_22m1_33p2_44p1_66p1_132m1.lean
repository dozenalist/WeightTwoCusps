module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 132

The eta expression is `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(22z)^(-1) η(33z)^2 η(44z) η(66z) η(132z)^(-1)`; see
[the local level table](../../TABLE.md#level-132).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(22z)^(-1) η(33z)^2 η(44z) η(66z) η(132z)^(-1)` at level 132. -/
abbrev cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -2, 1 => 6, 3 => -2, 21 => -1, 32 => 2, 43 => 1, 65 => 1, 131 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1 =
    [0, 1, 2, -1, -2, 1, -2, -2, 0, -2, 2, 1, 0, 0, -2, 3, 2, 2, 0, 0,
     2, -2, 0, 1, 4, -2, -2, 3, -4, -4, -2, -1, 0, 1, -4, -6, 2, 9, 0, 4,
     4, -4, 6, -6, -2, 2, 6, 2, -8, 1, -8, -2, -4, -4, 6, 1, -6, -8, 4, 9,
     -2, 8, 10, 0, 6, 0, -2, 1, 8, -1, -8, -1, -4, 0, 2, -2, 4, 0, -6, -10,
     2, 7, -8, 6, 4, 2, 0, -4, -2, 5, 0, 0, -6, -7, 0, -4, 4, -9, 2, 0] := by
  eta_coeff

end WeightTwoCusps
