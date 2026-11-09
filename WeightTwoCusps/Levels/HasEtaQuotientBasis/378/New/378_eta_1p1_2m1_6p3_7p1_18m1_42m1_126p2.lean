module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z) η(2z)^(-1) η(6z)^3 η(7z) η(18z)^(-1) η(42z)^(-1) η(126z)^2`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(6z)^3 η(7z) η(18z)^(-1) η(42z)^(-1) η(126z)^2` at level 378. -/
abbrev cuspForm_378_eta_1p1_2m1_6p3_7p1_18m1_42m1_126p2 : gamma0CuspForms 378 :=
  etaQuotientCuspForm 378 sparse![378; 0 => 1, 1 => -1, 5 => 3, 6 => 1, 17 => -1, 41 => -1, 125 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_378_eta_1p1_2m1_6p3_7p1_18m1_42m1_126p2_first_coeffs :
    first_coeffs 100 cuspForm_378_eta_1p1_2m1_6p3_7p1_18m1_42m1_126p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 1, -1, -2, 1, 3, 1, 0,
     0, 1, 2, -6, 1, -2, 3, 0, -2, 0, -1, -5, 0, -1, 0, 6, 3, 6, 0, 1,
     1, -6, -1, 3, 0, -1, -2, 0, -3, -2, -6, 2, 0, 6, -3, 5, -1, -3, 3, 3,
     0, -5, 3, 0, -4, -6, 3, -4, 3, 5, -1, 6, -1, -1, 0, 7, 5, -6, 6, 4,
     0, -5, -5, -6, -1, -1, 0, -5, 1, 3, -3, 5, -6, -2, 2, 0, -2, -1, 4, -8] := by
  eta_coeff

end WeightTwoCusps
