module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 102

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(17z) η(102z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(17z) η(102z)` at level 102. -/
abbrev cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1 : gamma0CuspForms 102 :=
  etaQuotientCuspForm 102 sparse![102; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 16 => 1, 101 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1 =
    [0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, 1, -2,
     1, -3, -2, -3, -3, -1, -2, 1, 0, -3, 0, 4, 4, 2, -1, -1, -1, 0, 3, 0,
     -2, 2, 2, 5, -2, 2, 4, -3, 4, -3, 4, -1, 0, 7, -3, 4, 5, 3, -2, -2,
     1, 0, -1, 2, 0, -4, 1, 3, 0, -1, 1, -3, -2, -4, -1, -2, -1, 0, 0, -4,
     -5, 3, 0, 4, -5, 0, -4, -3, 2, 1, -3, -4, 3, -5, 1, 0, 0, -2, -1, -3] := by
  eta_coeff

end WeightTwoCusps
