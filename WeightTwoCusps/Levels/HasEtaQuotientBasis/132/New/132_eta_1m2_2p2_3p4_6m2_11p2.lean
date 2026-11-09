module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 132

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(11z)^2`; see
[the local level table](../../TABLE.md#level-132).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 20 (zero-based) at level 264; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-264).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(11z)^2` at level 132. -/
abbrev cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 10 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2 =
    [0, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2, 1, -2, 0, -4, -1, 0, -2, 0, -8,
     -2, -2, -2, 3, -8, -4, -8, -3, 0, -8, -2, -5, -4, -1, -4, -2, 0, 3, 0, -8,
     -4, 8, 4, 2, 2, -6, 6, 0, 8, -3, -4, 10, -4, 2, -2, 1, 8, 8, 16, 1,
     2, 16, 10, 8, -4, 4, 2, 5, 4, -3, -4, 9, 12, 4, -6, 0, 8, -2, 8, 2,
     4, -3, 0, 10, -8, 6, 12, 0, 0, -17, 0, -8, 10, 13, -20, -8, 0, 9, 2, -2] := by
  eta_coeff

end WeightTwoCusps
