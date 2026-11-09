module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 154

The eta expression is `η(z)^(-1) η(2z)^2 η(7z)^(-1) η(11z)^2 η(14z)^2 η(22z)^(-1) η(77z)^2 η(154z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(7z)^(-1) η(11z)^2 η(14z)^2 η(22z)^(-1) η(77z)^2 η(154z)^(-1)` at level 154. -/
abbrev cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1 : gamma0CuspForms 154 :=
  etaQuotientCuspForm 154 sparse![154; 0 => -1, 1 => 2, 6 => -1, 10 => 2, 13 => 2, 21 => -1, 76 => 2, 153 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1 =
    [0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 2, -2, -2, 1, -2, 1, 0, -1, -2,
     -2, 0, -2, 2, 0, -1, 0, -2, 1, 0, 0, 0, 1, -4, -4, 0, -1, 2, 0, -2,
     -4, 0, 0, 0, 2, 2, 4, -2, -2, 1, 1, 2, 2, 4, -4, 0, 1, -4, 4, 0,
     0, -2, 2, 1, -3, 0, 4, 4, 0, -2, 0, 2, 3, 4, 0, -2, 2, 2, -6, 0,
     2, 3, -4, -2, -2, -6, 0, 4, -2, 4, 4, -2, 4, 0, 2, 2, 4, 4, 1, 2] := by
  eta_coeff

end WeightTwoCusps
