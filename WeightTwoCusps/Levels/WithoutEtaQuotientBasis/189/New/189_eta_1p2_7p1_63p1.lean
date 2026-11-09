module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 189

The eta expression is `η(z)^2 η(7z) η(63z)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(7z) η(63z)` at level 189. -/
abbrev cuspForm_189_eta_1p2_7p1_63p1 : gamma0CuspForms 189 :=
  etaQuotientCuspForm 189 sparse![189; 0 => 2, 6 => 1, 62 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_1p2_7p1_63p1_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_1p2_7p1_63p1 =
    [0, 0, 0, 1, -2, -1, 2, 1, 2, -2, -1, 0, -1, -1, -1, -2, 4, 2, 2, 5,
     -3, -1, -4, -2, -3, 4, -2, -2, 0, 4, 2, -5, 4, 1, 3, 0, 2, -2, 1, -2,
     0, -1, 1, -6, -2, 4, -6, -2, -1, 0, 2, 6, 6, -4, 2, 7, -1, 4, -4, 2,
     -4, -7, -1, 2, 0, 0, -4, 2, 2, -3, 1, 0, -6, -2, 2, -1, 6, 1, 2, 0,
     -3, -2, 1, 6, 1, 6, 6, 1, 0, -1, -4, -3, -8, 0, 9, -6, -2, -11, 0, -8] := by
  eta_coeff

end WeightTwoCusps
