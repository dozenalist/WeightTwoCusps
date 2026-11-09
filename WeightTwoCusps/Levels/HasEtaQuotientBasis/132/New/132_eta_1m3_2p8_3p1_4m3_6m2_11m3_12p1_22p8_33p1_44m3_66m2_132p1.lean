module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 132

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-2) η(11z)^(-3) η(12z) η(22z)^8 η(33z) η(44z)^(-3) η(66z)^(-2) η(132z)`; see
[the local level table](../../TABLE.md#level-132).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 17 (zero-based) at level 264; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-264).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-2) η(11z)^(-3) η(12z) η(22z)^8 η(33z) η(44z)^(-3) η(66z)^(-2) η(132z)` at level 132. -/
abbrev cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m3_12p1_22p8_33p1_44m3_66m2_132p1 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 10 => -3, 11 => 1, 21 => 8, 32 => 1, 43 => -3, 65 => -2, 131 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m3_12p1_22p8_33p1_44m3_66m2_132p1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m3_12p1_22p8_33p1_44m3_66m2_132p1 =
    [0, 0, 1, 3, 1, -3, -1, 0, -1, 0, -2, 0, -1, 0, 10, 0, -9, 0, 1, 0,
     -2, -6, 1, -3, -5, 9, -8, -6, 10, 6, 8, -9, -1, 3, -2, 6, 1, -3, 0, 12,
     8, 6, -10, 6, 1, -3, 20, -6, 15, 0, -7, -6, -8, 6, -7, -3, -10, 0, -18, -3,
     8, -12, -14, 0, 11, -12, -1, -3, -2, -6, -20, 3, -1, -6, 12, -3, 0, 0, 8, 12,
     12, 9, -2, 6, -10, 6, 0, 6, -1, -3, -2, 0, 20, 12, 14, 0, -5, 3, 21, 0] := by
  eta_coeff

end WeightTwoCusps
