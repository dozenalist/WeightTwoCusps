module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z) η(2z)^(-1) η(6z) η(7z) η(18z) η(42z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(6z) η(7z) η(18z) η(42z)` at level 378. -/
abbrev cuspForm_378_eta_1p1_2m1_6p1_7p1_18p1_42p1 : gamma0CuspForms 378 :=
  etaQuotientCuspForm 378 sparse![378; 0 => 1, 1 => -1, 5 => 1, 6 => 1, 17 => 1, 41 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_378_eta_1p1_2m1_6p1_7p1_18p1_42p1_first_coeffs :
    first_coeffs 100 cuspForm_378_eta_1p1_2m1_6p1_7p1_18p1_42p1 =
    [0, 0, 0, 1, -1, 0, -1, 1, -1, 0, -1, 3, -1, 2, -2, 2, -1, 0, -2, 3,
     -2, 0, -1, 3, -2, -1, -2, 4, -2, 0, -2, 2, -1, 1, -3, 6, -2, 0, -2, 4,
     -2, 0, 0, 6, -2, 1, -1, 0, -2, -2, -1, 4, -1, -3, -1, 1, -1, -4, -2, 6,
     0, -1, 2, 1, -1, -3, 0, 7, 0, -5, 0, 3, 0, -2, -1, 6, 3, -6, -2, 5,
     0, -6, 1, 6, -1, -8, 0, -1, 1, 0, 3, 6, 3, -2, 1, -3, 1, -11, 1, 8] := by
  eta_coeff

end WeightTwoCusps
