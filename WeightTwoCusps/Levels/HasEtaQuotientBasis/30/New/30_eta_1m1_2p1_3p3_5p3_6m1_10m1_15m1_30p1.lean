module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 30

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z) η(3z)^3 η(5z)^3 η(6z)^(-1) η(10z)^(-1) η(15z)^(-1) η(30z)`; see
[the local level table](../../TABLE.md#level-30).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 40 (zero-based) at level 330; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-330).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^3 η(5z)^3 η(6z)^(-1) η(10z)^(-1) η(15z)^(-1) η(30z)` at level 30. -/
abbrev cuspForm_30_eta_1m1_2p1_3p3_5p3_6m1_10m1_15m1_30p1 : gamma0CuspForms 30 :=
  etaQuotientCuspForm 30 sparse![30; 0 => -1, 1 => 1, 2 => 3, 4 => 3, 5 => -1, 9 => -1, 14 => -1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_30_eta_1m1_2p1_3p3_5p3_6m1_10m1_15m1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_30_eta_1m1_2p1_3p3_5p3_6m1_10m1_15m1_30p1 =
    [0, 1, 1, 1, -1, -1, -3, -4, -3, 1, 3, 0, 3, 2, 4, -1, 7, 6, 1, -4,
     -3, -4, -8, 0, 1, 1, -6, 1, -4, -6, -1, 8, -3, 0, -2, 4, -1, 2, 12, 2,
     -1, -6, 4, -4, 8, -1, 0, 0, -5, 9, 1, 6, 6, -6, -3, 0, 4, -4, 2, 0,
     1, -10, -8, -4, -9, -2, 8, -4, 2, 0, -4, 0, -3, 2, -22, 1, -12, 0, 2, 8,
     5, 1, 26, 12, -4, -6, 12, -6, 8, 18, 3, -8, 0, 8, 16, 4, 1, 2, -23, 0] := by
  eta_coeff

end WeightTwoCusps
