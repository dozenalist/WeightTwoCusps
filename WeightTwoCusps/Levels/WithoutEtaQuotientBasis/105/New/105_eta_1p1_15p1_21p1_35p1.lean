module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 105

The eta expression is `η(z) η(15z) η(21z) η(35z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-105).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(15z) η(21z) η(35z)` at level 105. -/
abbrev cuspForm_105_eta_1p1_15p1_21p1_35p1 : gamma0CuspForms 105 :=
  etaQuotientCuspForm 105 sparse![105; 0 => 1, 14 => 1, 20 => 1, 34 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_105_eta_1p1_15p1_21p1_35p1_first_coeffs :
    first_coeffs 100 cuspForm_105_eta_1p1_15p1_21p1_35p1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, -2, 1,
     1, 0, 0, -1, -1, 1, 1, 0, 0, 0, 1, -1, 0, 0, 1, 1, 1, 0, -3, 3,
     -2, -1, 0, -2, 0, -1, 1, 1, 1, 0, -1, -1, -1, 3, 0, -3, -1, 1, 2, 2,
     2, 0, -1, 0, 1, 1, 0, 0, 1, -3, -1, -2, -1, 1, -2, 2, 1, -1, 1, -2,
     0, -2, 1, 0, -1, 5, 2, 0, 2, -3, -1, 1, -1, -1, 0, -3, -2, 2, 0, -2] := by
  eta_coeff

end WeightTwoCusps
