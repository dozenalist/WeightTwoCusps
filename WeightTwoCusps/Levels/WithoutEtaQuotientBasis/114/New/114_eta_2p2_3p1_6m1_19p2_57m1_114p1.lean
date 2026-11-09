module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(2z)^2 η(3z) η(6z)^(-1) η(19z)^2 η(57z)^(-1) η(114z)`; see
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

/-- The cuspidal eta quotient `η(2z)^2 η(3z) η(6z)^(-1) η(19z)^2 η(57z)^(-1) η(114z)` at level 114. -/
abbrev cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 1 => 2, 2 => 1, 5 => -1, 18 => 2, 56 => -1, 113 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1 =
    [0, 0, 0, 0, 1, 0, -2, -1, -1, 2, 2, 1, 1, -3, 2, 1, -1, -1, -2, -1,
     -3, 1, 1, -1, 0, 5, 3, 2, -2, -3, -3, -2, 7, -4, -2, 1, 3, 4, 2, 3,
     -1, -5, -6, 1, -2, 0, 0, -4, -1, 1, -1, 2, -4, 2, 2, -1, 3, 1, 10, -4,
     7, 9, 1, -3, -9, -3, 2, -1, 2, 3, -13, 9, -3, -1, -5, -11, -3, -9, 5, 3,
     3, -8, 6, 12, 6, -3, 1, 2, -2, 7, 2, -2, -1, 5, 6, 1, -4, 7, -14, -11] := by
  eta_coeff

end WeightTwoCusps
