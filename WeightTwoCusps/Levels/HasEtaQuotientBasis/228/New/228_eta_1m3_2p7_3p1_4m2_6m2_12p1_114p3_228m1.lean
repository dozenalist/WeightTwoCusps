module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 228

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(114z)^3 η(228z)^(-1)`; see
[the local level table](../../TABLE.md#level-228).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 2 (zero-based) at level 456; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-456).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(114z)^3 η(228z)^(-1)` at level 228. -/
abbrev cuspForm_228_eta_1m3_2p7_3p1_4m2_6m2_12p1_114p3_228m1 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 113 => 3, 227 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m3_2p7_3p1_4m2_6m2_12p1_114p3_228m1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m3_2p7_3p1_4m2_6m2_12p1_114p3_228m1 =
    [0, 0, 0, 0, 0, 1, 3, 2, 0, 1, 0, 1, 3, 0, 0, -1, 0, 1, -3, 0,
     0, 0, 0, -2, 0, -2, 0, 1, 0, -2, -3, 0, 0, -1, 0, -1, -6, 0, 0, -1,
     0, 0, 3, -4, 0, 0, 0, 1, -3, 0, 0, 0, 0, -2, -3, 0, 0, 0, 0, 0,
     0, 2, 0, 1, 0, -2, 3, 0, 0, -1, 0, 0, 3, 0, 0, 1, 0, 3, -3, 0,
     0, 0, 0, 2, 3, 0, 0, 0, 0, 2, 0, 0, 0, -1, 0, -1, 6, 4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
