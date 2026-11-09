module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 72

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(3z)^3 η(4z) η(12z)`; see
[the local level table](../../TABLE.md#level-72).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 12 (zero-based) at level 144; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-144).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(4z) η(12z)` at level 72. -/
abbrev cuspForm_72_eta_1m1_3p3_4p1_12p1 : gamma0CuspForms 72 :=
  etaQuotientCuspForm 72 sparse![72; 0 => -1, 2 => 3, 3 => 1, 11 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_72_eta_1m1_3p3_4p1_12p1_first_coeffs :
    first_coeffs 100 cuspForm_72_eta_1m1_3p3_4p1_12p1 =
    [0, 1, 1, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -2, -4, -4, 0, -1, 0, -4,
     0, 0, 0, 4, 0, -1, 2, 2, 0, -3, 0, 8, 0, 8, 0, 0, 0, 6, 8, -4,
     0, 3, 0, 4, 0, 4, 0, 0, 0, -7, -5, 4, 0, 1, 0, -8, 0, -8, 0, -2,
     0, -2, -4, 0, 0, -2, 0, -4, 0, -16, 0, -4, 0, 10, -10, -2, 0, 0, 0, -8,
     0, -2, 0, 2, 0, -4, 8, 12, 0, 3, 0, 0, 0, 16, 0, -4, 0, 2, 9, -8] := by
  eta_coeff

end WeightTwoCusps
