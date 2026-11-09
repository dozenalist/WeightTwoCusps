module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 105

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(3z) η(5z)^3 η(7z)^3 η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-105).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

It is needed by table vector 17 (zero-based) at level 210; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-210).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(5z)^3 η(7z)^3 η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)` at level 105. -/
abbrev cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1 : gamma0CuspForms 105 :=
  etaQuotientCuspForm 105 sparse![105; 0 => -1, 2 => 1, 4 => 3, 6 => 3, 14 => -1, 20 => -1, 34 => -1, 104 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1_first_coeffs :
    first_coeffs 100 cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1 =
    [0, 0, 0, 1, 1, 2, 2, 4, 2, 4, 0, 4, -2, 1, -6, 3, -7, 0, -11, 2,
     -9, -3, -11, 4, -6, -3, -8, 2, 3, -7, -4, 4, 8, -8, -1, 0, 8, -14, -4, 9,
     14, 3, 4, 13, 19, 0, -2, 14, 8, -3, 3, 4, 12, -12, 1, 4, 4, -2, 12, -10,
     6, -14, 0, 6, -9, -7, 17, -5, -5, -14, 0, -1, -13, 2, 30, -2, 16, -4, 12, 17,
     -5, -14, 7, -11, -6, -12, -19, 7, -27, 7, -11, -5, -2, -8, -39, 18, -6, -3, 3, -15] := by
  eta_coeff

end WeightTwoCusps
