module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 102

The eta expression is `η(z)^2 η(3z)^(-1) η(6z) η(17z) η(34z)^(-1) η(102z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(3z)^(-1) η(6z) η(17z) η(34z)^(-1) η(102z)^2` at level 102. -/
abbrev cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2 : gamma0CuspForms 102 :=
  etaQuotientCuspForm 102 sparse![102; 0 => 2, 2 => -1, 5 => 1, 16 => 1, 33 => -1, 101 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 3, -1, 1, 1, -1, -1, 0, -2, -2,
     2, 1, 3, -1, 1, -1, 2, 0, -4, 2, -1, -2, -2, 3, 0, 1, 0, -1, -1, 0,
     3, -2, 2, 1, 1, 1, -4, -1, 2, 3, -4, 0, 2, -1, 0, 0, -3, -3, 3, -4,
     4, -1, -5, 4, 0, 0, 4, 7, -1, 1, 3, -3, -1, -4, 2, -2, 1, -8, 0, 8,
     -4, 1, 0, -2, -7, 1, 0, 4, 1, 3, 0, -4, 1, -1, 3, 2, -4, 8, 1, -6] := by
  eta_coeff

end WeightTwoCusps
