module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 132

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(33z)^(-2) η(66z)^6 η(132z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(33z)^(-2) η(66z)^6 η(132z)^(-2)` at level 132. -/
abbrev cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 32 => -2, 65 => 6, 131 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2 =
    [0, 0, 0, 1, 4, 4, -2, -4, 0, 3, 4, 0, -2, -4, -8, 1, 4, 0, -2, -8,
     0, 2, 0, 4, -4, -4, 0, 2, 4, 0, -2, -4, -8, 1, 8, 0, 2, 4, 8, 0,
     -4, 8, 4, 8, 0, -1, -4, -16, 0, 0, 0, -2, -12, 0, 0, 0, 8, -8, 0, 12,
     2, 4, 0, -2, -4, -16, 2, 12, -8, 3, -8, -4, 8, 8, 16, -4, 0, 0, 8, 4,
     8, -3, -16, 0, 0, 16, -8, -8, 0, -4, 2, 16, 24, -5, -4, 8, 4, 4, 8, -1] := by
  eta_coeff

end WeightTwoCusps
