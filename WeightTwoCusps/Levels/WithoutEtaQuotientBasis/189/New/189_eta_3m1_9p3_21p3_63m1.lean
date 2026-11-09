module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 189

The eta expression is `η(3z)^(-1) η(9z)^3 η(21z)^3 η(63z)^(-1)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-189).
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(9z)^3 η(21z)^3 η(63z)^(-1)` at level 189. -/
abbrev cuspForm_189_eta_3m1_9p3_21p3_63m1 : gamma0CuspForms 189 :=
  etaQuotientCuspForm 189 sparse![189; 2 => -1, 8 => 3, 20 => 3, 62 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_3m1_9p3_21p3_63m1_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_3m1_9p3_21p3_63m1 =
    [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2,
     0, 0, -3, 0, 0, -2, 0, 0, -4, 0, 0, 2, 0, 0, -6, 0, 0, -1, 0, 0,
     -6, 0, 0, 2, 0, 0, -3, 0, 0, -3, 0, 0, -4, 0, 0, 0, 0, 0, -6, 0,
     0, 2, 0, 0, 1, 0, 0, 8, 0, 0, 3, 0, 0, -4, 0, 0, 14, 0, 0, 8,
     0, 0, 6, 0, 0, -6, 0, 0, -3, 0, 0, 10, 0, 0, 6, 0, 0, -10, 0, 0] := by
  eta_coeff

end WeightTwoCusps
