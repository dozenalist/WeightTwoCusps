module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 108

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-1) η(6z)^(-2) η(9z)^(-1) η(18z) η(36z)`; see
[the local level table](../../TABLE.md#level-108).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 12 (zero-based) at level 216; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-216).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-1) η(6z)^(-2) η(9z)^(-1) η(18z) η(36z)` at level 108. -/
abbrev cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1 : gamma0CuspForms 108 :=
  etaQuotientCuspForm 108 sparse![108; 0 => -3, 1 => 5, 2 => 4, 3 => -1, 5 => -2, 8 => -1, 17 => 1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1 =
    [0, 0, 1, 3, 4, 3, 0, 0, 1, 0, 0, -3, 0, 0, -1, 0, -8, 0, 0, 0,
     -3, -12, 0, -6, 0, 0, -4, 0, -4, 6, 0, 0, 1, 0, 0, -3, 0, 0, 2, 6,
     0, -6, 0, 0, 3, 0, 0, 6, 0, 0, 4, 0, 20, 9, 0, 0, -1, 24, 0, 12,
     0, 0, 5, 0, 16, -12, 0, 0, 0, 0, 0, 0, 0, 0, 2, -15, -28, 3, 0, 0,
     -3, 0, 0, -3, 0, 0, -10, 0, 0, -18, 0, 0, 6, -12, 0, 6, 0, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
