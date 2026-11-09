module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(2z) η(3z)^2 η(6z)^(-1) η(19z) η(57z)^(-1) η(114z)^2`; see
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

/-- The cuspidal eta quotient `η(2z) η(3z)^2 η(6z)^(-1) η(19z) η(57z)^(-1) η(114z)^2` at level 114. -/
abbrev cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 1 => 1, 2 => 2, 5 => -1, 18 => 1, 56 => -1, 113 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, -2, -1, 2, 0, 2, 0, 0, 1, 0,
     2, -2, -1, 0, -2, -2, 0, -1, 0, 1, 4, 1, -3, 0, 0, 0, 0, 1, -1, 0,
     2, 3, 0, 2, 0, -2, -1, 0, 1, -2, -1, -1, 1, -4, 0, -2, -1, 1, -6, 4,
     -2, 0, 2, 2, 4, 3, 2, -1, -2, 1, 5, -1, 2, 0, 2, -3, 1, 2, -5, -4,
     -2, 0, 2, -2, -3, 0, -1, 6, 2, -5, -3, 0, 0, 0, -1, -1, 2, -1, 6, 2] := by
  eta_coeff

end WeightTwoCusps
