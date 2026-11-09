module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 195

The eta expression is `η(z)^2 η(3z)^(-1) η(5z)^(-1) η(13z)^(-1) η(15z)^2 η(39z)^2 η(65z)^2 η(195z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(3z)^(-1) η(5z)^(-1) η(13z)^(-1) η(15z)^2 η(39z)^2 η(65z)^2 η(195z)^(-1)` at level 195. -/
abbrev cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1 : gamma0CuspForms 195 :=
  etaQuotientCuspForm 195 sparse![195; 0 => 2, 2 => -1, 4 => -1, 12 => -1, 14 => 2, 38 => 2, 64 => 2, 194 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1 =
    [0, 1, -2, -1, 3, -1, 2, 0, -4, 1, 2, 0, -3, 0, 1, -1, 4, 1, -3, 4,
     -3, -4, 1, 0, 4, -2, 0, 1, -3, 3, 2, -2, 0, -3, -4, 2, 5, 4, -9, 0,
     4, 0, 9, -3, -3, -1, -2, -2, -4, 2, 6, -3, 0, 3, -3, 2, 3, -3, -5, 1,
     -3, 0, 7, 2, -7, 0, 6, 3, 8, -3, -7, 0, -5, -1, -7, -4, 14, 7, 0, 1,
     -4, -2, 0, -4, -13, -1, 8, 1, 3, 8, 1, 0, 5, -3, 3, -4, 0, -5, -2, 1] := by
  eta_coeff

end WeightTwoCusps
