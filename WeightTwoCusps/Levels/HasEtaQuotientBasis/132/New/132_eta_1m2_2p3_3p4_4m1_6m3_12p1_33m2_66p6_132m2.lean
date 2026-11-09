module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 132

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^3 η(3z)^4 η(4z)^(-1) η(6z)^(-3) η(12z) η(33z)^(-2) η(66z)^6 η(132z)^(-2)`; see
[the local level table](../../TABLE.md#level-132).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 29 (zero-based) at level 264; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-264).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^4 η(4z)^(-1) η(6z)^(-3) η(12z) η(33z)^(-2) η(66z)^6 η(132z)^(-2)` at level 132. -/
abbrev cuspForm_132_eta_1m2_2p3_3p4_4m1_6m3_12p1_33m2_66p6_132m2 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -3, 11 => 1, 32 => -2, 65 => 6, 131 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m2_2p3_3p4_4m1_6m3_12p1_33m2_66p6_132m2_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m2_2p3_3p4_4m1_6m3_12p1_33m2_66p6_132m2 =
    [0, 0, 0, 1, 2, 2, 0, -2, 0, 1, 2, 0, -2, -2, -4, 1, 2, 0, -2, -4,
     0, 0, 0, 2, -2, -2, 0, 0, 2, 0, 0, -2, -4, 1, 4, 0, 2, 2, 4, 2,
     -2, 4, 0, 4, 0, -1, -2, -8, 2, 0, 0, -2, -6, 0, -2, 0, 4, -4, 0, 6,
     0, 2, 0, 0, -2, -8, 2, 6, -4, 1, -4, -2, 4, 4, 8, -4, 0, 0, 8, 2,
     4, 1, -8, 0, 2, 8, -4, -4, 0, -2, 0, 8, 12, 1, -2, 4, -2, 2, 4, -1] := by
  eta_coeff

end WeightTwoCusps
