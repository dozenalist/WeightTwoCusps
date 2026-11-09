module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 84

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(7z)^(-1) η(14z)^2 η(21z)^2 η(28z)^(-1) η(42z)^(-2) η(84z)^2`; see
[the local level table](../../TABLE.md#level-84).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 19 (zero-based) at level 252; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-252).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(7z)^(-1) η(14z)^2 η(21z)^2 η(28z)^(-1) η(42z)^(-2) η(84z)^2` at level 84. -/
abbrev cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2 : gamma0CuspForms 84 :=
  etaQuotientCuspForm 84 sparse![84; 0 => -3, 1 => 8, 3 => -3, 6 => -1, 13 => 2, 20 => 2, 27 => -1, 41 => -2, 83 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2 =
    [0, 0, 0, 0, 0, 1, 3, 1, -2, 2, 1, -4, 0, 1, 1, 0, -2, 0, -6, -3,
     -1, 0, 4, -6, 1, -2, -7, -1, -1, 6, -2, 6, 4, -6, 0, -1, 6, 2, 5, 6,
     5, 8, 1, -2, 8, 1, -6, 10, -2, 0, -2, -2, -5, -8, 6, 0, 3, -6, -2, -3,
     -4, -9, -2, 3, -4, 2, -2, 4, -12, -2, -1, 2, -8, -8, 10, 0, 7, -4, -4, 0,
     3, -2, 8, -3, -4, -2, 6, 8, -4, 14, 1, 3, -6, 8, -6, 0, 7, -6, 0, -4] := by
  eta_coeff

end WeightTwoCusps
