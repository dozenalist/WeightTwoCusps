module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 63

The eta expression is `η(3z)^2 η(21z)^2`; see
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

/-- The cuspidal eta quotient `η(3z)^2 η(21z)^2` at level 63. -/
abbrev cuspForm_63_eta_3p2_21p2 : gamma0CuspForms 63 :=
  etaQuotientCuspForm 63 sparse![63; 2 => 2, 20 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_63_eta_3p2_21p2_first_coeffs :
    first_coeffs 100 cuspForm_63_eta_3p2_21p2 =
    [0, 0, 1, 0, 0, -2, 0, 0, -1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0,
     -2, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0, 0, -3, 0, 0, -2, 0, 0, -4, 0,
     0, 6, 0, 0, 2, 0, 0, 4, 0, 0, 7, 0, 0, -4, 0, 0, -1, 0, 0, -4,
     0, 0, -4, 0, 0, -4, 0, 0, 2, 0, 0, -6, 0, 0, 2, 0, 0, 2, 0, 0,
     10, 0, 0, 0, 0, 0, -4, 0, 0, -2, 0, 0, -2, 0, 0, 8, 0, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
