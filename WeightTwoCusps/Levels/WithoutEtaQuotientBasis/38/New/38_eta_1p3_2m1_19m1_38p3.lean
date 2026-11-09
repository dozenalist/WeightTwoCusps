module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 38

The eta expression is `η(z)^3 η(2z)^(-1) η(19z)^(-1) η(38z)^3`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-38).
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

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-1) η(19z)^(-1) η(38z)^3` at level 38. -/
abbrev cuspForm_38_eta_1p3_2m1_19m1_38p3 : gamma0CuspForms 38 :=
  etaQuotientCuspForm 38 sparse![38; 0 => 3, 1 => -1, 18 => -1, 37 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_38_eta_1p3_2m1_19m1_38p3_first_coeffs :
    first_coeffs 100 cuspForm_38_eta_1p3_2m1_19m1_38p3 =
    [0, 0, 0, 0, 1, -3, 1, 2, 2, -1, -4, 1, -2, 0, 2, 4, -1, 2, -2, -1,
     0, -2, -2, -1, -3, 5, 3, 2, 1, -6, 6, -2, -2, 2, 4, -5, 0, -2, -1, -3,
     2, -2, -3, 1, 4, 3, 0, 5, 2, 4, 2, -4, -4, -4, -1, -7, 0, 1, -5, 8,
     -2, 3, -2, -3, 3, 6, 2, 2, -1, 0, -4, 0, 0, 8, -2, -2, 0, 3, -4, -6,
     -6, 4, 0, -6, 0, -3, 4, 5, 4, -2, 2, -2, -1, 2, 6, 1, 5, -2, 4, -5] := by
  eta_coeff

end WeightTwoCusps
