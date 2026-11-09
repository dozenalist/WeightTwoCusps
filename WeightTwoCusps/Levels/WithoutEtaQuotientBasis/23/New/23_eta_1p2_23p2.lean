module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 23

The eta expression is `η(z)^2 η(23z)^2`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-23).
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

/-- The cuspidal eta quotient `η(z)^2 η(23z)^2` at level 23. -/
abbrev cuspForm_23_eta_1p2_23p2 : gamma0CuspForms 23 :=
  etaQuotientCuspForm 23 sparse![23; 0 => 2, 22 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_23_eta_1p2_23p2_first_coeffs :
    first_coeffs 100 cuspForm_23_eta_1p2_23p2 =
    [0, 0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0,
     0, -2, -2, 0, 0, -4, 3, 2, -2, 0, -6, 6, 1, 6, 4, 0, -2, -2, -2, -6,
     2, -4, -4, 0, 4, 4, 1, -2, 3, 4, 3, -6, -3, 4, -1, -4, -2, 4, -3, 4,
     4, -8, -3, 4, -2, 6, 2, 2, -2, -2, 4, 2, -4, -4, 2, -2, 2, -8, 3, -8,
     -6, 0, 3, 2, 6, 8, 0, 6, 6, -4, -4, 6, -1, 0, 1, -4, -9, 6, -3, -4] := by
  eta_coeff

end WeightTwoCusps
