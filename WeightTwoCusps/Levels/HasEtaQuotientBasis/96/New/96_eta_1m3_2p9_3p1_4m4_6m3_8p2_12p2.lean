module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 96

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-4) η(6z)^(-3) η(8z)^2 η(12z)^2`; see
[the local level table](../../TABLE.md#level-96).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 4 (zero-based) at level 192; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-192).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-4) η(6z)^(-3) η(8z)^2 η(12z)^2` at level 96. -/
abbrev cuspForm_96_eta_1m3_2p9_3p1_4m4_6m3_8p2_12p2 : gamma0CuspForms 96 :=
  etaQuotientCuspForm 96 sparse![96; 0 => -3, 1 => 9, 2 => 1, 3 => -4, 5 => -3, 7 => 2, 11 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m3_2p9_3p1_4m4_6m3_8p2_12p2_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m3_2p9_3p1_4m4_6m3_8p2_12p2 =
    [0, 1, 3, 0, -6, -2, 3, 0, 0, -3, -6, 0, 6, 6, 0, 0, 0, 2, 3, 0,
     12, 0, -12, 0, 0, -1, -6, 0, 0, -10, -6, 0, 0, 0, 6, 0, -6, -2, 12, 0,
     0, 10, 0, 0, -24, 6, 24, 0, 0, -7, -3, 0, 12, 14, 3, 0, 0, 0, 18, 0,
     -12, -10, -24, 0, 0, -12, -12, 0, -12, 0, 0, 0, 0, -6, 18, 0, 24, 0, -6, 0,
     0, 9, -18, 0, 0, -4, -12, 0, 0, 10, -6, 0, 48, 0, 0, 0, 0, 18, -21, 0] := by
  eta_coeff

end WeightTwoCusps
