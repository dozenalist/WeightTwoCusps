module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 63

The eta expression is `η(z)^(-1) η(3z)^4 η(7z) η(9z)^(-1) η(63z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-63).
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^4 η(7z) η(9z)^(-1) η(63z)` at level 63. -/
abbrev cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1 : gamma0CuspForms 63 :=
  etaQuotientCuspForm 63 sparse![63; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_first_coeffs :
    first_coeffs 100 cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1 =
    [0, 0, 0, 1, 1, 2, -1, 1, -1, 1, -4, -3, -1, 2, -1, -2, -2, 2, -1, -4,
     0, -1, 5, 1, 3, 4, -2, 1, 0, 1, 2, -2, 4, 4, 0, 0, -1, -2, 4, -2,
     6, -4, 1, 0, 1, -2, -3, -2, -1, 0, -4, -6, 0, -1, -1, -2, 2, 4, -1, -4,
     2, -4, 2, -1, -3, 0, -4, -4, -4, 0, -2, 3, 3, 10, 2, -1, 0, 1, 2, 12,
     -6, 1, 10, 6, 1, -12, 0, -2, -9, 8, 2, 0, 1, 0, 6, 0, -5, -2, 0, 4] := by
  eta_coeff

end WeightTwoCusps
