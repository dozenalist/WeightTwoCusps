module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 154

The eta expression is `η(2z) η(7z) η(11z)^2 η(22z)^(-1) η(77z)^(-1) η(154z)^2`; see
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

/-- The cuspidal eta quotient `η(2z) η(7z) η(11z)^2 η(22z)^(-1) η(77z)^(-1) η(154z)^2` at level 154. -/
abbrev cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2 : gamma0CuspForms 154 :=
  etaQuotientCuspForm 154 sparse![154; 1 => 1, 6 => 1, 10 => 2, 21 => -1, 76 => -1, 153 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, -1, 0, 1,
     1, -1, 0, 2, 0, 2, 1, -1, 3, 0, -2, -3, -2, 0, -2, 0, 0, -2, 1, -2,
     -1, 1, 2, 0, 0, 5, 0, 0, 1, 1, 0, 2, -2, 0, 4, 1, -4, 0, -2, 0,
     2, -4, 1, 1, 2, -2, -2, 0, -1, -1, -2, -2, 6, -1, 2, -3, -1, 0, -4, 2,
     1, 0, -2, -1, -4, 2, 2, 4, 0, 1, -1, 1, 2, -2, 1, 0, 2, 3, 2, 2] := by
  eta_coeff

end WeightTwoCusps
