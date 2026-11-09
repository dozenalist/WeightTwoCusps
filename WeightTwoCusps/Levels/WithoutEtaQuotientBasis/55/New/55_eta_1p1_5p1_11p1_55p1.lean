module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 55

The eta expression is `η(z) η(5z) η(11z) η(55z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-55).
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

/-- The cuspidal eta quotient `η(z) η(5z) η(11z) η(55z)` at level 55. -/
abbrev cuspForm_55_eta_1p1_5p1_11p1_55p1 : gamma0CuspForms 55 :=
  etaQuotientCuspForm 55 sparse![55; 0 => 1, 4 => 1, 10 => 1, 54 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_55_eta_1p1_5p1_11p1_55p1_first_coeffs :
    first_coeffs 100 cuspForm_55_eta_1p1_5p1_11p1_55p1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 0, 1, 2, 0, 0, -2, 0, 0, 1, 0, -2, 0,
     -1, -2, 0, 1, 2, 0, 2, 1, 2, 2, -2, -1, -2, 1, -2, 2, -3, 1, 0, -4,
     0, 2, 0, 0, -1, 1, 0, -2, 2, 0, 0, 2, 2, 0, 2, -1, 0, 0, 0, -3,
     2, 2, 2, -2, 1, -2, 0, -1, -2, 1, -4, -3, 0, -2, 2, 1, 0, 0, 0, 2,
     3, 0, -4, 0, 0, 2, 0, 4, 0, 1, -2, 4, 0, 1, 2, 0, -2, -1, 0, 1] := by
  eta_coeff

end WeightTwoCusps
