module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 99

The eta expression is `η(z) η(9z) η(11z) η(99z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-99).
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

/-- The cuspidal eta quotient `η(z) η(9z) η(11z) η(99z)` at level 99. -/
abbrev cuspForm_99_eta_1p1_9p1_11p1_99p1 : gamma0CuspForms 99 :=
  etaQuotientCuspForm 99 sparse![99; 0 => 1, 8 => 1, 10 => 1, 98 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_99_eta_1p1_9p1_11p1_99p1_first_coeffs :
    first_coeffs 100 cuspForm_99_eta_1p1_9p1_11p1_99p1 =
    [0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, -1, 1, 0, 0, 1, -1,
     -1, -2, 0, -2, 1, 2, 0, -1, 1, 2, 0, 2, 0, 0, 0, 0, -1, -2, -1, 2,
     -3, 2, 0, 1, 0, -1, -2, 0, -1, -2, 2, 0, 0, -1, 1, 1, 3, 0, 2, 0,
     0, -2, 2, 2, 0, -2, -1, 2, 0, -3, 0, 0, -1, 2, -2, -1, 1, -1, -2, -1,
     -1, 2, 2, -4, 0, -2, 1, 2, 0, 1, 0, 2, 2, 5, 0, -4, 1, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
