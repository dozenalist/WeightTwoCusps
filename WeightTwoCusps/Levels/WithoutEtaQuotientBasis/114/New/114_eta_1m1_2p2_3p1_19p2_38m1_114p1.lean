module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(19z)^2 η(38z)^(-1) η(114z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(19z)^2 η(38z)^(-1) η(114z)` at level 114. -/
abbrev cuspForm_114_eta_1m1_2p2_3p1_19p2_38m1_114p1 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 0 => -1, 1 => 2, 2 => 1, 18 => 2, 37 => -1, 113 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1m1_2p2_3p1_19p2_38m1_114p1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1m1_2p2_3p1_19p2_38m1_114p1 =
    [0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1, -1, 0, -2, 1, 0, -1, -1, 0,
     2, 0, 0, 0, -2, -2, 2, 1, 2, 0, 3, 2, 0, 5, -2, 1, 2, 2, 0, -5,
     0, 2, -1, 0, -2, -4, -2, -1, 1, -2, 0, -2, -2, -2, -1, 0, -2, 0, 2, 0,
     -4, 2, 0, 3, 0, 0, 1, -2, 0, -1, 4, 2, 5, -2, 0, 5, 0, -1, -1, 0,
     0, 4, 4, 2, 1, 0, 0, -2, 0, 0, -8, 0, 2, -1, -4, -1, 6, 2, 2, 0] := by
  eta_coeff

end WeightTwoCusps
