module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 108

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-3) η(12z) η(18z)`; see
[the local level table](../../TABLE.md#level-108).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 5 (zero-based) at level 216; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-216).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-3) η(12z) η(18z)` at level 108. -/
abbrev cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1 : gamma0CuspForms 108 :=
  etaQuotientCuspForm 108 sparse![108; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -3, 11 => 1, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1 =
    [0, 1, 4, 6, 4, 0, 0, 5, 4, 0, 0, 0, 0, -7, -4, 0, -8, 0, 0, -1,
     -12, -24, 0, 0, 0, -5, -16, 0, -4, 0, 0, -4, 4, 0, 0, 0, 0, -1, 8, 12,
     0, 0, 0, 8, 12, 0, 0, 0, 0, 18, 16, 0, 20, 0, 0, 0, -4, 48, 0, 0,
     0, -13, 20, 0, 16, 0, 0, 11, 0, 0, 0, 0, 0, 17, 8, -30, -28, 0, 0, -13,
     -12, 0, 0, 0, 0, 0, -40, 0, 0, 0, 0, -35, 24, -24, 0, 0, 0, 5, -24, 0] := by
  eta_coeff

end WeightTwoCusps
