module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 98

The eta expression is `η(z) η(7z) η(14z) η(98z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-98).
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

/-- The cuspidal eta quotient `η(z) η(7z) η(14z) η(98z)` at level 98. -/
abbrev cuspForm_98_eta_1p1_7p1_14p1_98p1 : gamma0CuspForms 98 :=
  etaQuotientCuspForm 98 sparse![98; 0 => 1, 6 => 1, 13 => 1, 97 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_1p1_7p1_14p1_98p1_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_1p1_7p1_14p1_98p1 =
    [0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 1, 1, 0, 0, -2, 0, -3,
     1, 2, 0, 0, -1, 0, -1, 1, -1, 0, 0, 4, 0, 1, 1, 0, 0, 0, -2, 0,
     1, -5, -2, 0, 0, -1, 0, 4, 0, -1, 0, 0, 1, 0, 3, -2, 1, 0, 0, 1,
     0, -1, 2, -1, 0, 0, 1, 0, -2, 2, 0, 0, 0, -1, 0, -4, -3, 0, 0, 0,
     1, 0, -2, 5, 2, 0, 0, -4, 0, -1, -1, 4, 0, 0, -2, 0, -1, 6, 1, 0] := by
  eta_coeff

end WeightTwoCusps
