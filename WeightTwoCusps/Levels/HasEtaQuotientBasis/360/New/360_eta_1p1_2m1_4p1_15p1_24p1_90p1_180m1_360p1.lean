module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(z) η(2z)^(-1) η(4z) η(15z) η(24z) η(90z) η(180z)^(-1) η(360z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(4z) η(15z) η(24z) η(90z) η(180z)^(-1) η(360z)` at level 360. -/
abbrev cuspForm_360_eta_1p1_2m1_4p1_15p1_24p1_90p1_180m1_360p1 : gamma0CuspForms 360 :=
  etaQuotientCuspForm 360 sparse![360; 0 => 1, 1 => -1, 3 => 1, 14 => 1, 23 => 1, 89 => 1, 179 => -1, 359 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_360_eta_1p1_2m1_4p1_15p1_24p1_90p1_180m1_360p1_first_coeffs :
    first_coeffs 100 cuspForm_360_eta_1p1_2m1_4p1_15p1_24p1_90p1_180m1_360p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, 0, 1,
     0, 0, 0, 1, 0, 0, 0, 0, -2, 1, 0, 1, 0, 0, -2, 0, 0, -1, 0, 0,
     1, 1, 0, -1, 1, 0, 1, -1, 0, 1, 0, 0, 2, -2, 0, -1, -1, 0, 2, 0,
     0, -1, 2, 0, 1, -1, 0, -1, -2, 0, -1, -2, 0, 0, 0, 0, 2, 0, 0, -1,
     1, 0, 2, 1, 0, 0, 1, 0, 2, -2, 0, 0, 0, 0, -1, 1, 0, -2, 2, 0] := by
  eta_coeff

end WeightTwoCusps
