module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 175

The eta expression is `η(z) η(25z) η(35z)^2`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-175).
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

/-- The cuspidal eta quotient `η(z) η(25z) η(35z)^2` at level 175. -/
abbrev cuspForm_175_eta_1p1_25p1_35p2 : gamma0CuspForms 175 :=
  etaQuotientCuspForm 175 sparse![175; 0 => 1, 24 => 1, 34 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_175_eta_1p1_25p1_35p2_first_coeffs :
    first_coeffs 100 cuspForm_175_eta_1p1_25p1_35p2 =
    [0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 2, 1, 0, 0, -1, 0, -1, 0, 0, -3,
     2, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, -1,
     0, -2, 0, 0, 3, -4, -1, 0, 0, 4, 0, 2, 0, 0, 0, 1, -2, 0, 0, -1,
     -2, -2, 0, 0, 0, 0, 2, 0, 0, 4, -2, -2, 0, 0, 3, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
