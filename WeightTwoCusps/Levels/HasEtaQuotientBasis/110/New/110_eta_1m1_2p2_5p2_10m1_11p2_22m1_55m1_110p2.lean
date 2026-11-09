module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 110

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z)^2 η(5z)^2 η(10z)^(-1) η(11z)^2 η(22z)^(-1) η(55z)^(-1) η(110z)^2`; see
[the local level table](../../TABLE.md#level-110).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 56 (zero-based) at level 330; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-330).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(5z)^2 η(10z)^(-1) η(11z)^2 η(22z)^(-1) η(55z)^(-1) η(110z)^2` at level 110. -/
abbrev cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 10 => 2, 21 => -1, 54 => -1, 109 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -2, -1, 0, -2, 0, 1, -4, -2,
     0, -2, -1, 4, 2, 0, 4, 0, 1, 4, 2, 0, 0, 2, 0, 1, 0, 2, 0, -6,
     -2, -4, 2, 1, 0, 0, -2, 0, -4, 0, 0, 6, 1, -6, 0, 0, -4, -4, -2, -4,
     0, 2, -4, 5, 4, 1, -2, -6, 3, 4, -2, 0, 9, -3, -2, 0, -2, -1, 10, 4,
     -2, 8, 2, -3, 2, 3, 4, 4, 2, 4, 1, 4, 2, 0, -6, -2, -8, -2, -2, 0] := by
  eta_coeff

end WeightTwoCusps
