module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 105

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(3z)^3 η(5z) η(7z) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)^3`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-105).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

It is needed by table vector 24 (zero-based) at level 210; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-210).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(5z) η(7z) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)^3` at level 105. -/
abbrev cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3 : gamma0CuspForms 105 :=
  etaQuotientCuspForm 105 sparse![105; 0 => -1, 2 => 3, 4 => 1, 6 => 1, 14 => -1, 20 => -1, 34 => -1, 104 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3_first_coeffs :
    first_coeffs 100 cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 1, -3, 0,
     -2, 0, -5, 0, -2, -1, -4, 0, 2, 0, -2, 0, 4, -2, 1, -2, 7, -2, 0, -1,
     4, -5, 0, -1, 7, 2, 0, 5, 1, 1, 1, 0, 0, 2, -1, 3, -4, -2, 4, -2,
     1, 0, 0, -2, -8, -4, 7, -5, -3, 0, 2, 1, -7, -2, 6, -1, 4, 5, 4, 6,
     -2, 1, 5, -3, -3, -5, -7, 1, -5, -1, -3, 4, 4, 0, -11, 4, -4, 0, -1, 2] := by
  eta_coeff

end WeightTwoCusps
