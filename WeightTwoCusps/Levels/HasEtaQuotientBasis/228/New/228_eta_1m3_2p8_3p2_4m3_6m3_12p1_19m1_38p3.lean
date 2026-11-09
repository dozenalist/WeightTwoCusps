module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 228

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^8 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z) η(19z)^(-1) η(38z)^3`; see
[the local level table](../../TABLE.md#level-228).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 9 (zero-based) at level 456; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-456).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z) η(19z)^(-1) η(38z)^3` at level 228. -/
abbrev cuspForm_228_eta_1m3_2p8_3p2_4m3_6m3_12p1_19m1_38p3 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 0 => -3, 1 => 8, 2 => 2, 3 => -3, 5 => -3, 11 => 1, 18 => -1, 37 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m3_2p8_3p2_4m3_6m3_12p1_19m1_38p3_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m3_2p8_3p2_4m3_6m3_12p1_19m1_38p3 =
    [0, 0, 0, 0, 1, 3, 1, -4, -4, -1, 2, 1, -2, 0, -4, -2, 5, 2, 4, -1,
     0, 4, -2, 5, 3, -1, -3, -4, 1, 0, 0, -2, -2, -10, -2, 7, 0, 4, -1, 3,
     2, -2, 3, -5, -2, 3, 0, -1, -4, -2, 2, 2, 2, 2, -1, -1, 0, 1, 1, -4,
     4, -3, -2, 3, -3, -6, -10, 8, -1, 0, 8, 6, 0, 2, 10, 4, 0, -9, 8, 0,
     0, -2, -6, 6, 0, 3, 4, -1, -2, -2, -4, -2, -1, 2, -12, 1, -1, -2, -2, -11] := by
  eta_coeff

end WeightTwoCusps
