module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 110

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-1) η(11z)^3 η(22z)^(-1) η(55z)^(-1) η(110z)`; see
[the local level table](../../TABLE.md#level-110).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 17 (zero-based) at level 330; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-330).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-1) η(11z)^3 η(22z)^(-1) η(55z)^(-1) η(110z)` at level 110. -/
abbrev cuspForm_110_eta_1m1_2p1_5p3_10m1_11p3_22m1_55m1_110p1 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 10 => 3, 21 => -1, 54 => -1, 109 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1m1_2p1_5p3_10m1_11p3_22m1_55m1_110p1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1m1_2p1_5p3_10m1_11p3_22m1_55m1_110p1 =
    [0, 0, 0, 1, 1, 1, 2, 2, 0, 1, 2, 0, 2, 2, -2, -2, -1, -6, -4, 2,
     -3, -4, 0, -5, -4, 0, -2, -3, 4, -4, -4, 3, -2, 1, 0, -4, -3, 5, -2, 0,
     8, -2, -2, 0, -3, 5, 8, 6, 0, 10, 0, 4, 2, -2, 12, 1, -2, 2, 10, -1,
     4, 8, 0, 6, 7, 2, 2, 9, 8, -13, -2, -7, -10, -6, 4, 1, -6, 2, -12, -14,
     -7, 0, -4, 4, -6, -4, 0, -10, 0, 5, -8, 0, 4, -7, -6, 6, 0, -11, -10, -7] := by
  eta_coeff

end WeightTwoCusps
