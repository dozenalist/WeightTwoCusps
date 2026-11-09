module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 96

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(24z)^2`; see
[the local level table](../../TABLE.md#level-96).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 16 (zero-based) at level 288; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-288).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(24z)^2` at level 96. -/
abbrev cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2 : gamma0CuspForms 96 :=
  etaQuotientCuspForm 96 sparse![96; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 23 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2 =
    [0, 0, 1, 3, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, 0, -6, 0, 0, 1, 0,
     -4, 0, -4, 0, 0, 0, -2, -9, 0, 0, -2, 0, 0, 0, 2, 0, 2, 0, 4, 18,
     0, 0, 0, 0, 8, 0, 8, 0, 0, 0, -1, 6, -4, 0, 1, 0, 0, 0, 6, 0,
     4, 0, -8, 0, 0, 0, -4, 0, 4, 0, 0, 0, 0, 0, 6, -3, -8, 0, -2, 0,
     0, 0, -6, 0, 0, 0, -4, -30, 0, 0, -2, 0, -16, 0, 0, 0, 0, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
