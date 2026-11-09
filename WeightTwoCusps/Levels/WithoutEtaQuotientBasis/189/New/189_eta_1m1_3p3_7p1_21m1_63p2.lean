module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 189

The eta expression is `η(z)^(-1) η(3z)^3 η(7z) η(21z)^(-1) η(63z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(7z) η(21z)^(-1) η(63z)^2` at level 189. -/
abbrev cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2 : gamma0CuspForms 189 :=
  etaQuotientCuspForm 189 sparse![189; 0 => -1, 2 => 3, 6 => 1, 20 => -1, 62 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2 =
    [0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 1, 2, -1, 0, 0, 2, -2, 1, -2, 1,
     -2, -1, 0, -2, -3, 0, 0, 2, -3, -2, 4, 1, 0, -4, -2, 1, -2, -2, 0, -2,
     1, -1, -1, -2, -4, -4, 2, 3, 2, -1, 0, 6, 2, -2, -2, -1, 0, 4, -4, 3,
     -2, 2, 0, -2, 0, -4, -5, 2, -2, 0, 0, 0, 6, 0, 0, -4, -3, 2, -2, 0,
     4, 2, 1, 1, 0, -2, 0, 2, 2, 2, 4, 9, 4, 2, 2, 2, 5, 2, 0, 8] := by
  eta_coeff

end WeightTwoCusps
