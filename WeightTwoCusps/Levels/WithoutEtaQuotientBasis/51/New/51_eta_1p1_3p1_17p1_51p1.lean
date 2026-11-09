module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 51

The eta expression is `η(z) η(3z) η(17z) η(51z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-51).
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

/-- The cuspidal eta quotient `η(z) η(3z) η(17z) η(51z)` at level 51. -/
abbrev cuspForm_51_eta_1p1_3p1_17p1_51p1 : gamma0CuspForms 51 :=
  etaQuotientCuspForm 51 sparse![51; 0 => 1, 2 => 1, 16 => 1, 50 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_first_coeffs :
    first_coeffs 100 cuspForm_51_eta_1p1_3p1_17p1_51p1 =
    [0, 0, 0, 1, -1, -1, -1, 1, 2, -1, 2, 0, 0, -1, -1, -1, -1, 0, 1, -1,
     -2, 3, 1, 2, 1, -1, 0, -2, -1, 2, 0, 1, 0, 0, 0, -2, 0, 0, -2, -1,
     2, -1, -3, 1, -1, 1, -1, 2, 0, 4, 4, 1, 0, 0, 2, -1, 3, -3, -6, -4,
     4, -4, 1, -3, 1, 1, -1, 0, -1, 2, 2, -1, -1, 0, -2, 0, 4, 0, 2, 3,
     -4, 2, 0, 0, -3, -1, 2, 4, 1, 2, 0, -2, 1, 3, -4, 5, -5, 2, -4, 0] := by
  eta_coeff

end WeightTwoCusps
