module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 66

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(11z)^(-1) η(22z)^3 η(33z) η(66z)^(-1)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-66).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

It is needed by table vector 62 (zero-based) at level 462; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-462).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(11z)^(-1) η(22z)^3 η(33z) η(66z)^(-1)` at level 66. -/
abbrev cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1 : gamma0CuspForms 66 :=
  etaQuotientCuspForm 66 sparse![66; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 10 => -1, 21 => 3, 32 => 1, 65 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1 =
    [0, 1, 1, -1, -1, -2, -1, 1, 0, 1, -2, 1, 4, 1, 1, -1, -1, -2, 1, 0,
     -1, -1, 1, 2, -3, 2, 1, 2, -1, 0, -1, -5, 2, -1, -2, -2, -1, 3, 0, -1,
     3, -2, -1, 0, -1, -2, 2, 5, 4, 3, 2, 2, -1, 3, 2, -2, -9, 0, 0, -1,
     1, 3, -5, 1, 7, -2, -1, -7, 2, -5, -2, 0, 0, -8, 3, 7, 0, 1, -1, -1,
     -1, -2, -2, 6, -5, 4, 0, 6, 0, 3, -2, -8, -5, -4, 5, 0, 1, -1, 3, 1] := by
  eta_coeff

end WeightTwoCusps
