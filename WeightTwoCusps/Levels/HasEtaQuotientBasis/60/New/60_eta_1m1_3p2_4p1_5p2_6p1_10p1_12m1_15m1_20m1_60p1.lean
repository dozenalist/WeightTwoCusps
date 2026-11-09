module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 60

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(5z)^2 η(6z) η(10z) η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(60z)`; see
[the local level table](../../TABLE.md#level-60).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 40 (zero-based) at level 300; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-300).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(5z)^2 η(6z) η(10z) η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(60z)` at level 60. -/
abbrev cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1 : gamma0CuspForms 60 :=
  etaQuotientCuspForm 60 sparse![60; 0 => -1, 2 => 2, 3 => 1, 4 => 2, 5 => 1, 9 => 1, 11 => -1, 14 => -1, 19 => -1, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1 =
    [0, 0, 1, 1, 2, 1, 2, 0, -1, -2, -2, -2, -5, -2, -6, -2, -6, 2, 1, 4,
     5, 4, 2, -2, 4, 0, 4, -1, 6, -2, -1, 0, 11, 2, 8, 0, 2, -6, -8, 4,
     -4, 4, -6, 6, -14, 3, 0, 6, 3, -4, 1, -12, -10, -2, 2, -2, -6, -8, -8, -6,
     -2, 0, 12, -4, -2, 0, -2, 6, -2, 10, 6, 0, -1, 4, 8, 1, 20, 0, 2, -4,
     -3, 8, -14, 2, 6, 0, -8, 12, 10, -4, -2, 0, 0, -8, -4, 0, -8, 0, 17, -2] := by
  eta_coeff

end WeightTwoCusps
