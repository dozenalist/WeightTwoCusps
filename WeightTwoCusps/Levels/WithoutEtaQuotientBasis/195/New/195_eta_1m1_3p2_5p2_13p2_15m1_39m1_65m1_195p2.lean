module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 195

The eta expression is `η(z)^(-1) η(3z)^2 η(5z)^2 η(13z)^2 η(15z)^(-1) η(39z)^(-1) η(65z)^(-1) η(195z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(5z)^2 η(13z)^2 η(15z)^(-1) η(39z)^(-1) η(65z)^(-1) η(195z)^2` at level 195. -/
abbrev cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2 : gamma0CuspForms 195 :=
  etaQuotientCuspForm 195 sparse![195; 0 => -1, 2 => 2, 4 => 2, 12 => 2, 14 => -1, 38 => -1, 64 => -1, 194 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 3, 1, 2,
     0, 4, 1, 2, 0, 3, -2, -2, -3, 3, -4, 0, -2, 3, -8, -2, -2, 4, -5, -1,
     0, -4, -11, -5, -3, 0, -6, 0, -1, -3, -8, -1, 3, 5, 5, -2, 3, -3, -7, 1,
     6, 8, -1, -2, 2, -1, -8, 3, 14, 1, 5, -4, 1, -9, -9, 3, 8, -1, 2, -3,
     -1, 3, 12, 2, 19, -3, 12, -7, 3, 0, 1, 0, 11, 5, -1, -2, 2, 1, 12, -1] := by
  eta_coeff

end WeightTwoCusps
