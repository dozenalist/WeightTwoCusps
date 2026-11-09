module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 126

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(7z)^(-2) η(9z)^(-2) η(14z) η(18z) η(21z)^7 η(42z)^(-3) η(63z)^(-2) η(126z)`; see
[the local level table](../../TABLE.md#level-126).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 25 (zero-based) at level 252; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-252).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(7z)^(-2) η(9z)^(-2) η(14z) η(18z) η(21z)^7 η(42z)^(-3) η(63z)^(-2) η(126z)` at level 126. -/
abbrev cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p1_18p1_21p7_42m3_63m2_126p1 : gamma0CuspForms 126 :=
  etaQuotientCuspForm 126 sparse![126; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 6 => -2, 8 => -2, 13 => 1, 17 => 1, 20 => 7, 41 => -3, 62 => -2, 125 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p1_18p1_21p7_42m3_63m2_126p1_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p1_18p1_21p7_42m3_63m2_126p1 =
    [0, 1, 2, 4, 1, 0, -4, 1, 2, 4, 6, 0, 4, -10, 2, 0, 7, 12, -4, 8,
     -24, 4, -6, 0, -4, -17, 16, -20, 1, -12, 0, -4, -22, 0, -18, 0, 4, 2, -20, -16,
     -6, 12, -4, 20, 24, 0, 6, -24, 4, 1, 38, 24, -10, 12, 20, 12, 2, 8, 12, -12,
     0, 26, -8, 4, 1, 0, 0, -4, 36, 0, 6, 0, -4, -10, 4, -20, 8, 0, 16, 8,
     24, 28, -30, -12, 4, 12, -32, -24, 6, -12, 0, -10, -24, -16, 12, 0, -4, -34, 2, 0] := by
  eta_coeff

end WeightTwoCusps
