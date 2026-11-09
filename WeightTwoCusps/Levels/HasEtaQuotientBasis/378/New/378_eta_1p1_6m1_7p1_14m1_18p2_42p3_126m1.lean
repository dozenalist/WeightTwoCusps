module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z) η(6z)^(-1) η(7z) η(14z)^(-1) η(18z)^2 η(42z)^3 η(126z)^(-1)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(6z)^(-1) η(7z) η(14z)^(-1) η(18z)^2 η(42z)^3 η(126z)^(-1)` at level 378. -/
abbrev cuspForm_378_eta_1p1_6m1_7p1_14m1_18p2_42p3_126m1 : gamma0CuspForms 378 :=
  etaQuotientCuspForm 378 sparse![378; 0 => 1, 5 => -1, 6 => 1, 13 => -1, 17 => 2, 41 => 3, 125 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_378_eta_1p1_6m1_7p1_14m1_18p2_42p3_126m1_first_coeffs :
    first_coeffs 100 cuspForm_378_eta_1p1_6m1_7p1_14m1_18p2_42p3_126m1 =
    [0, 1, -1, -1, 0, 0, 1, 1, -1, 0, 1, 0, 1, 0, -2, -2, 0, 0, 2, -1,
     0, 0, 0, 3, 2, -1, -2, -4, -2, 3, 2, 0, -1, -1, 1, 6, 2, -1, -2, -4,
     0, 0, 0, -4, 0, -1, 0, 6, 2, -1, -1, -4, -3, 3, 1, -1, -2, 4, 0, 6,
     0, 3, -2, -1, 0, -6, 0, 1, 0, 5, 1, -3, 0, -2, -2, -6, -1, -6, 2, 3,
     0, 6, 1, 6, 1, 2, 1, 1, 2, -12, -3, 4, 3, 2, 1, 0, -1, 1, 3, -8] := by
  eta_coeff

end WeightTwoCusps
