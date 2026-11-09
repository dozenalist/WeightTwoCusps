module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 132

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(11z) η(12z) η(33z)^(-1) η(66z)^3 η(132z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(11z) η(12z) η(33z)^(-1) η(66z)^3 η(132z)^(-1)` at level 132. -/
abbrev cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 10 => 1, 11 => 1, 32 => -1, 65 => 3, 131 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1 =
    [0, 0, 1, 3, 3, 1, -1, 0, 3, 2, 2, 0, -3, -2, -4, 0, -1, -2, 1, -6,
     -2, -2, -1, 3, -3, -1, -6, -4, 4, 0, -2, -5, -5, 1, 2, 2, 3, -1, 4, 2,
     -2, 8, 4, 8, 1, -5, 4, -8, 1, 0, -1, 0, -10, 4, -1, -1, 4, 2, 6, 1,
     2, 2, 0, 4, -1, -8, 1, 5, -2, -2, -8, 1, 3, 2, 6, -5, 4, 0, 6, 8,
     6, 1, -6, 2, -4, 10, 4, 0, 1, -9, 2, 4, 20, 14, -12, 4, 5, 9, 9, -2] := by
  eta_coeff

end WeightTwoCusps
