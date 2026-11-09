module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 66

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(11z)^(-1) η(22z)^2 η(33z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-66).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

It is needed by table vector 58 (zero-based) at level 462; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-462).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(11z)^(-1) η(22z)^2 η(33z)` at level 66. -/
abbrev cuspForm_66_eta_1m1_2p2_3p1_11m1_22p2_33p1 : gamma0CuspForms 66 :=
  etaQuotientCuspForm 66 sparse![66; 0 => -1, 1 => 2, 2 => 1, 10 => -1, 21 => 2, 32 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p2_3p1_11m1_22p2_33p1_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p2_3p1_11m1_22p2_33p1 =
    [0, 0, 0, 1, 1, 0, 0, -1, 0, -1, -1, 0, -2, 1, 1, 0, -1, 0, 1, 0,
     -1, -1, 0, -2, 3, 1, -1, -1, 1, 2, 0, 1, 0, 1, 0, 2, 1, -1, 0, 3,
     -1, 0, -1, 0, 1, -1, 1, -1, -2, -2, 2, -2, 1, -1, -1, 0, 1, 0, 0, 1,
     -1, -1, -4, 1, -1, -2, 0, -1, -2, 0, 0, 0, -2, 2, 0, -2, 0, -1, 1, 1,
     1, 4, 2, -2, 1, 0, 2, 0, 0, 3, 0, 0, 3, 3, -1, 0, 1, -1, 2, -1] := by
  eta_coeff

end WeightTwoCusps
