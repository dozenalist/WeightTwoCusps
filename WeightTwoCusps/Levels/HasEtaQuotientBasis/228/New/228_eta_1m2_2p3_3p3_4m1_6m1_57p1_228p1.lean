module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 228

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-1) η(57z) η(228z)`; see
[the local level table](../../TABLE.md#level-228).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 18 (zero-based) at level 456; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-456).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-1) η(57z) η(228z)` at level 228. -/
abbrev cuspForm_228_eta_1m2_2p3_3p3_4m1_6m1_57p1_228p1 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 56 => 1, 227 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m2_2p3_3p3_4m1_6m1_57p1_228p1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m2_2p3_3p3_4m1_6m1_57p1_228p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 2, 1, 0,
     0, 0, 2, -2, 0, 0, -2, 1, 0, 2, -2, -4, 0, -1, 0, 0, -2, 0, 0, 0,
     -2, -2, 0, 0, -2, -2, 0, -2, 1, 0, 0, -2, 0, 0, 0, 0, -2, 1, -4, 0,
     0, 0, 2, 0, 0, -2, -2, 2, 2, -1, -2, -2, -1, 0, -2, -3, 0, 2, 1, -2,
     2, 0, 0, 4, 1, 0, -4, 4, 4, -2, 4, 0, 2, 2, 4, 0, -2, 2, 2, 2] := by
  eta_coeff

end WeightTwoCusps
