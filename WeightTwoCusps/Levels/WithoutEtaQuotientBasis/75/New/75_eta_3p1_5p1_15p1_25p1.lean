module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 75

The eta expression is `η(3z) η(5z) η(15z) η(25z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-75).
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

/-- The cuspidal eta quotient `η(3z) η(5z) η(15z) η(25z)` at level 75. -/
abbrev cuspForm_75_eta_3p1_5p1_15p1_25p1 : gamma0CuspForms 75 :=
  etaQuotientCuspForm 75 sparse![75; 2 => 1, 4 => 1, 14 => 1, 24 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_75_eta_3p1_5p1_15p1_25p1_first_coeffs :
    first_coeffs 100 cuspForm_75_eta_3p1_5p1_15p1_25p1 =
    [0, 0, 1, 0, 0, -1, 0, -1, -1, 0, 1, 0, -1, 1, 0, 1, 0, 0, 1, 0,
     1, 0, 0, 2, 0, -1, 0, 0, -2, 0, -1, 0, -1, -2, 0, 0, 0, 4, -2, 0,
     -3, 0, 2, -1, 0, -1, 0, -2, 1, 0, 1, 0, 0, 2, 0, 4, 0, 3, 6, 0,
     -1, 0, -2, -1, 0, 2, 0, -5, 2, 0, 0, 0, -1, -8, 0, 1, 0, -2, 0, 0,
     1, 0, -2, -2, 0, -2, 0, -4, 4, 0, 1, 0, 4, 1, 0, -4, 0, 5, -1, 0] := by
  eta_coeff

end WeightTwoCusps
