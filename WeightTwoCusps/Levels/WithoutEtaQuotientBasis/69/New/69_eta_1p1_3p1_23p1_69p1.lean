module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 69

The eta expression is `η(z) η(3z) η(23z) η(69z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-69).
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

/-- The cuspidal eta quotient `η(z) η(3z) η(23z) η(69z)` at level 69. -/
abbrev cuspForm_69_eta_1p1_3p1_23p1_69p1 : gamma0CuspForms 69 :=
  etaQuotientCuspForm 69 sparse![69; 0 => 1, 2 => 1, 22 => 1, 68 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_69_eta_1p1_3p1_23p1_69p1_first_coeffs :
    first_coeffs 100 cuspForm_69_eta_1p1_3p1_23p1_69p1 =
    [0, 0, 0, 0, 1, -1, -1, -1, 1, 2, -1, 2, 0, 0, -1, -1, -1, -1, 0, 1,
     -1, -1, 2, 0, 1, 2, 1, -2, 1, 0, 3, -2, -2, 0, -3, 0, -1, 0, 1, 0,
     -1, 2, 1, 1, 0, -1, 0, 0, -2, -2, 2, 3, 3, -1, -2, 0, 1, -1, -1, 0,
     1, 2, 1, 3, -2, -4, 0, 1, -3, 0, 0, -4, -1, -2, -2, 2, 1, 4, -4, 3,
     1, 0, 3, 2, 1, 2, 3, 0, -2, 3, 3, -4, 1, -4, -1, 0, 1, -4, -2, -6] := by
  eta_coeff

end WeightTwoCusps
