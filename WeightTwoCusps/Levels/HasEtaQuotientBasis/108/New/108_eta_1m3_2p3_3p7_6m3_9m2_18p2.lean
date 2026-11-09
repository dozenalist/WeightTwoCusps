module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 108

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(18z)^2`; see
[the local level table](../../TABLE.md#level-108).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 10 (zero-based) at level 216; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-216).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(18z)^2` at level 108. -/
abbrev cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2 : gamma0CuspForms 108 :=
  etaQuotientCuspForm 108 sparse![108; 0 => -3, 1 => 3, 2 => 7, 5 => -3, 8 => -2, 17 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2 =
    [0, 1, 3, 6, 6, 3, 0, -1, 3, 0, 0, -3, 0, 5, -3, 0, -12, 0, 0, -7,
     -9, -24, 0, -6, 0, -5, -12, 0, -6, 6, 0, -4, 3, 0, 0, -3, 0, 11, 6, 12,
     0, -6, 0, 8, 9, 0, 0, 6, 0, -6, 12, 0, 30, 9, 0, 0, -3, 48, 0, 12,
     0, -1, 15, 0, 24, -12, 0, 5, 0, 0, 0, 0, 0, -7, 6, -30, -42, 3, 0, 17,
     -9, 0, 0, -3, 0, 0, -30, 0, 0, -18, 0, -5, 18, -24, 0, 6, 0, -19, -18, 0] := by
  eta_coeff

end WeightTwoCusps
