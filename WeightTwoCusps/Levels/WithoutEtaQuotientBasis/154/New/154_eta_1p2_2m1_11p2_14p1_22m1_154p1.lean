module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 154

The eta expression is `η(z)^2 η(2z)^(-1) η(11z)^2 η(14z) η(22z)^(-1) η(154z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-154).
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(11z)^2 η(14z) η(22z)^(-1) η(154z)` at level 154. -/
abbrev cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1 : gamma0CuspForms 154 :=
  etaQuotientCuspForm 154 sparse![154; 0 => 2, 1 => -1, 10 => 2, 13 => 1, 21 => -1, 153 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -2, 0, -2, 4,
     0, -1, -2, 2, 0, -2, 0, 4, 0, 0, 2, 0, 0, -4, -4, -1, 6, -2, 0, -2,
     0, -4, 0, 6, 2, 0, 4, -4, 4, 0, 4, 0, -4, 0, -4, 0, -2, -6, 0, 0,
     -2, 0, 4, 0, 0, -2, 4, 8, 4, -4, 2, -4, 0, 0, 4, 0, -4, 1, -2, -2,
     4, -6, 0, -4, 2, -2, -2, 4, 0, 4, 4, 0, -4, 2, 0, -8, 4, 4, 0, 2] := by
  eta_coeff

end WeightTwoCusps
