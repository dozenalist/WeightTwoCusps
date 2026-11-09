module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 102

The eta expression is `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(17z)^3 η(34z)^(-1) η(51z)^(-1) η(102z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(17z)^3 η(34z)^(-1) η(51z)^(-1) η(102z)` at level 102. -/
abbrev cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1 : gamma0CuspForms 102 :=
  etaQuotientCuspForm 102 sparse![102; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 16 => 3, 33 => -1, 50 => -1, 101 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1 =
    [0, 0, 0, 1, 1, 1, -1, -1, 0, -1, 0, -2, 0, -1, -1, 1, -1, 0, 1, 1,
     -2, -5, -3, 4, 3, 3, 4, 0, 5, 2, 4, 3, -4, 4, 0, -4, -2, -2, 8, 1,
     -4, -3, -9, -3, -1, 1, -7, -4, -2, 2, -4, -1, 4, -2, 4, -3, 3, -3, 4, 4,
     -6, 2, -7, 3, -1, -1, 7, -2, 3, 4, 4, 3, -3, 0, 6, -2, 6, 8, 2, -3,
     12, 4, 4, -4, 5, -1, -10, 2, -3, 4, -4, 2, -11, -1, 2, -1, 7, -10, -10, -8] := by
  eta_coeff

end WeightTwoCusps
