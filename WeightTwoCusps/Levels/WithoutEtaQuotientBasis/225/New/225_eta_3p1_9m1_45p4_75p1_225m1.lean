module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 225

The eta expression is `η(3z) η(9z)^(-1) η(45z)^4 η(75z) η(225z)^(-1)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-225).
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

/-- The cuspidal eta quotient `η(3z) η(9z)^(-1) η(45z)^4 η(75z) η(225z)^(-1)` at level 225. -/
abbrev cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1 : gamma0CuspForms 225 :=
  etaQuotientCuspForm 225 sparse![225; 2 => 1, 8 => -1, 44 => 4, 74 => 1, 224 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1 =
    [0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 2,
     0, 0, -1, 0, 0, -1, 0, 0, 3, 0, 0, -2, 0, 0, -1, 0, 0, 4, 0, 0,
     -3, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, -2, 0,
     0, -4, 0, 0, 2, 0, 0, -3, 0, 0, 0, 0, 0, 2, 0, 0, -3, 0, 0, -1,
     0, 0, 3, 0, 0, -2, 0, 0, 2, 0, 0, 6, 0, 0, -5, 0, 0, -3, 0, 0] := by
  eta_coeff

end WeightTwoCusps
