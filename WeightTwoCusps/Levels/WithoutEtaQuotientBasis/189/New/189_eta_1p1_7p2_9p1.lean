module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 189

The eta expression is `η(z) η(7z)^2 η(9z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-189).
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

/-- The cuspidal eta quotient `η(z) η(7z)^2 η(9z)` at level 189. -/
abbrev cuspForm_189_eta_1p1_7p2_9p1 : gamma0CuspForms 189 :=
  etaQuotientCuspForm 189 sparse![189; 0 => 1, 6 => 2, 8 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_1p1_7p2_9p1_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_1p1_7p2_9p1 =
    [0, 1, -1, -1, 0, 0, 1, 0, -1, 2, 1, 1, 1, -3, 0, -4, 0, 2, -2, -3,
     2, 1, 4, 1, 0, 0, 0, 2, -2, 2, -2, 1, -1, 5, -3, -1, -2, -5, -6, 2,
     0, -2, 2, 5, 3, -4, 6, -2, 1, 1, 0, 0, 2, -4, -2, 11, 2, -4, 4, 2,
     -2, -3, -4, -2, -8, -2, 4, -6, 2, -3, -1, -3, 6, 4, 5, 1, -10, 0, 4, -1,
     8, 2, -1, 0, -1, 3, -2, -1, 0, 6, 4, -1, 7, 0, -9, 1, -7, 1, -1, 8] := by
  eta_coeff

end WeightTwoCusps
