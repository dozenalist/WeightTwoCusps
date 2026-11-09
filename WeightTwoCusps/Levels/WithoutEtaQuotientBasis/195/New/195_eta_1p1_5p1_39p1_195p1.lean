module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 195

The eta expression is `η(z) η(5z) η(39z) η(195z)`; see
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

/-- The cuspidal eta quotient `η(z) η(5z) η(39z) η(195z)` at level 195. -/
abbrev cuspForm_195_eta_1p1_5p1_39p1_195p1 : gamma0CuspForms 195 :=
  etaQuotientCuspForm 195 sparse![195; 0 => 1, 4 => 1, 38 => 1, 194 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1p1_5p1_39p1_195p1_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1p1_5p1_39p1_195p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 0, 1, 2, 0, 0,
     -2, 1, -1, 0, 0, -2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, -2, 0, 0,
     1, -1, 0, 0, 0, 0, -2, -2, 0, -1, 1, 1, 1, 0, 0, 1, -2, 0, 0, 2,
     -1, 3, 0, 0, 2, 0, -1, 2, 0, -1, -2, -1, 0, 0, -2, -2, 2, -2, 0, -1,
     -1, 0, 1, 0, 0, 2, 4, 0, -1, 1, 1, -1, 0, 0, -3, -2, 0, 2, 2, -1] := by
  eta_coeff

end WeightTwoCusps
