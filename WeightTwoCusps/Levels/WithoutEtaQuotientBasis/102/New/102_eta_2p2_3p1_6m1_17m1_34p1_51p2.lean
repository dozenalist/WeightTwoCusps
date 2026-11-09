module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 102

The eta expression is `η(2z)^2 η(3z) η(6z)^(-1) η(17z)^(-1) η(34z) η(51z)^2`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-102).
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

/-- The cuspidal eta quotient `η(2z)^2 η(3z) η(6z)^(-1) η(17z)^(-1) η(34z) η(51z)^2` at level 102. -/
abbrev cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2 : gamma0CuspForms 102 :=
  etaQuotientCuspForm 102 sparse![102; 1 => 2, 2 => 1, 5 => -1, 16 => -1, 33 => 1, 50 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2 =
    [0, 0, 0, 0, 0, 1, 0, -2, -1, -1, 2, 2, 1, 1, -3, 2, 1, -1, -1, -2,
     -1, -3, 2, 1, -1, -1, 0, 3, 2, 3, 2, -4, 2, 2, -1, -1, -3, 0, -3, 2,
     -2, 0, -4, -3, 4, 0, 4, 1, -2, 5, 2, -1, 0, -5, 3, -4, 1, -1, 2, -2,
     -3, 4, -1, 6, 0, -2, 1, 3, 0, -1, -3, 3, -2, 0, -3, 0, -5, -4, 2, 0,
     5, -1, -2, 0, 5, 0, -2, 1, 4, -3, 1, 0, -1, -5, -3, 2, 4, 6, 7, -7] := by
  eta_coeff

end WeightTwoCusps
