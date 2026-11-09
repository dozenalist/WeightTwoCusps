module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 102

The eta expression is `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(34z) η(51z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-102).
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

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(34z) η(51z)` at level 102. -/
abbrev cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1 : gamma0CuspForms 102 :=
  etaQuotientCuspForm 102 sparse![102; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 33 => 1, 50 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1 =
    [0, 0, 0, 0, 1, -3, 2, 1, -1, -1, 3, -1, 0, -2, -2, 2, 0, 0, 1, 3,
     0, -2, -2, 1, -1, 0, 2, 1, -1, 0, -3, -1, -2, 3, 0, 3, 0, 1, 1, 3,
     -5, -1, 1, 0, -2, -2, -1, 5, 1, -1, 0, 0, -2, -1, -3, 1, 6, -2, -1, 0,
     2, -7, 2, 1, 7, 7, 1, -5, 0, -5, -3, -2, -4, 4, 0, -3, 1, 0, -4, 7,
     4, 3, 4, -2, -4, 0, -2, -6, 0, 1, 0, 2, 4, 0, -5, 1, 6, 2, -3, -4] := by
  eta_coeff

end WeightTwoCusps
