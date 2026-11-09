module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 195

The eta expression is `η(3z) η(13z) η(15z) η(65z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-195).
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

/-- The cuspidal eta quotient `η(3z) η(13z) η(15z) η(65z)` at level 195. -/
abbrev cuspForm_195_eta_3p1_13p1_15p1_65p1 : gamma0CuspForms 195 :=
  etaQuotientCuspForm 195 sparse![195; 2 => 1, 12 => 1, 14 => 1, 64 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_3p1_13p1_15p1_65p1_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_3p1_13p1_15p1_65p1 =
    [0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0,
     1, 0, 1, 1, 0, 2, 0, 0, 0, 0, -1, 0, 0, 1, -2, -1, 1, 1, -2, 0,
     -1, 0, 0, 0, 0, 0, 0, 2, -1, -2, -1, -2, 0, 1, 0, 0, 0, 0, 0, 0,
     2, 0, 2, -1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, -1, 0, 2,
     0, 0, 1, -2, 0, -3, 0, 0, -1, 0, -1, 0, -2, 0, 1, 2, -2, -1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
