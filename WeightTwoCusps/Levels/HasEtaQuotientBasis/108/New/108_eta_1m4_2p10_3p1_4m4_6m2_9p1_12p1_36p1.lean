module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 108

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(9z) η(12z) η(36z)`; see
[the local level table](../../TABLE.md#level-108).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 7 (zero-based) at level 216; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-216).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(9z) η(12z) η(36z)` at level 108. -/
abbrev cuspForm_108_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_36p1 : gamma0CuspForms 108 :=
  etaQuotientCuspForm 108 sparse![108; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 8 => 1, 11 => 1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_36p1 =
    [0, 0, 1, 4, 4, -1, 0, 4, 1, 0, 0, 1, 0, -8, -1, 0, -8, 0, 0, 4,
     -3, -16, 0, 2, 0, 0, -4, 0, -4, -2, 0, 0, 1, 0, 0, 1, 0, -8, 2, 8,
     0, 2, 0, 0, 3, 0, 0, -2, 0, 16, 4, 0, 20, -3, 0, 0, -1, 32, 0, -4,
     0, -8, 5, 0, 16, 4, 0, 4, 0, 0, 0, 0, 0, 16, 2, -20, -28, -1, 0, -20,
     -3, 0, 0, 1, 0, 0, -10, 0, 0, 6, 0, -20, 6, -16, 0, -2, 0, 16, -6, 0] := by
  eta_coeff

end WeightTwoCusps
