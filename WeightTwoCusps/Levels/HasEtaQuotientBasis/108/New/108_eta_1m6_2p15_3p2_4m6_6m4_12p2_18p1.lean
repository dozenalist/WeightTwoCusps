module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 108

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-4) η(12z)^2 η(18z)`; see
[the local level table](../../TABLE.md#level-108).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 2 (zero-based) at level 216; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-216).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-4) η(12z)^2 η(18z)` at level 108. -/
abbrev cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1 : gamma0CuspForms 108 :=
  etaQuotientCuspForm 108 sparse![108; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -4, 11 => 2, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1 =
    [0, 1, 6, 12, 6, -6, 0, 11, 6, 0, 0, 6, 0, -19, -6, 0, -12, 0, 0, 5,
     -18, -48, 0, 12, 0, -5, -24, 0, -6, -12, 0, -4, 6, 0, 0, 6, 0, -13, 12, 24,
     0, 12, 0, 8, 18, 0, 0, -12, 0, 42, 24, 0, 30, -18, 0, 0, -6, 96, 0, -24,
     0, -25, 30, 0, 24, 24, 0, 17, 0, 0, 0, 0, 0, 41, 12, -60, -42, -6, 0, -43,
     -18, 0, 0, 6, 0, 0, -60, 0, 0, 36, 0, -65, 36, -48, 0, -12, 0, 29, -36, 0] := by
  eta_coeff

end WeightTwoCusps
