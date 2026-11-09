module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(19z) η(38z)^(-1) η(114z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(19z) η(38z)^(-1) η(114z)^2` at level 114. -/
abbrev cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 0 => -1, 1 => 1, 2 => 2, 18 => 1, 37 => -1, 113 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, -1, 0, -1, 0, 0,
     -1, 0, -2, -1, 1, 0, -1, -1, -2, -1, -2, 1, 0, -2, 1, 1, 0, -1, 0, 2,
     1, 2, 1, -2, 2, 1, 2, 0, 0, 2, -2, 2, 2, 1, 0, 0, 1, 0, 0, -1,
     1, 0, 1, -1, 0, 0, 1, -1, -2, 1, -2, -2, -2, 0, 3, 0, 0, 1, -1, 3,
     1, -2, -2, 0, 0, 0, 2, 2, -2, 0, 3, 1, -3, -2, 1, 0, -3, 0, -5, -2] := by
  eta_coeff

end WeightTwoCusps
