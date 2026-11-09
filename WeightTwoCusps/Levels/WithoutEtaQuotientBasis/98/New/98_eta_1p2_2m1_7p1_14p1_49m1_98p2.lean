module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 98

The eta expression is `η(z)^2 η(2z)^(-1) η(7z) η(14z) η(49z)^(-1) η(98z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(7z) η(14z) η(49z)^(-1) η(98z)^2` at level 98. -/
abbrev cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2 : gamma0CuspForms 98 :=
  etaQuotientCuspForm 98 sparse![98; 0 => 2, 1 => -1, 6 => 1, 13 => 1, 48 => -1, 97 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, -1, 2, -2, 0, -2, 0,
     0, -2, 4, 4, 0, -4, 0, 0, 1, -2, 2, 0, 0, 0, 0, 0, 0, -6, 0, 2,
     0, 0, 2, -2, 2, 0, 8, 0, 0, 1, -4, -4, 0, 0, 0, 0, -1, -6, 2, 0,
     2, 0, 0, 1, 4, 0, 0, -6, 0, 0, 0, 10, 4, 0, -10, 0, 0, 0, -2, 6,
     0, 2, 0, 0, -2, 2, -12, 0, -4, 0, 0, -4, 4, 8, 0, 10, 0, 0, -1, -4] := by
  eta_coeff

end WeightTwoCusps
