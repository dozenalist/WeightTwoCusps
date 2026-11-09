module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(19z) η(114z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-114).
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

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(19z) η(114z)` at level 114. -/
abbrev cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 18 => 1, 113 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1 =
    [0, 0, 0, 0, 0, 0, 1, -3, 2, 1, -1, -1, 3, -1, 0, -2, -2, 2, 0, 0,
     1, 3, 0, -2, -2, 0, 2, -2, 1, 2, 0, -3, -2, -1, 0, 5, -2, 3, 0, 0,
     -1, 0, -1, 2, -2, 3, -1, -6, -1, 5, -4, 5, 1, 4, -2, 0, -6, 0, -1, -4,
     -1, 4, 5, -4, 2, 0, 3, 4, -1, -1, 2, 0, 2, -3, -5, -1, 0, -5, -3, 1,
     5, -1, 6, 2, -2, 0, -4, -4, 4, -2, -1, 0, 4, 0, 5, 0, 2, -4, 4, 2] := by
  eta_coeff

end WeightTwoCusps
