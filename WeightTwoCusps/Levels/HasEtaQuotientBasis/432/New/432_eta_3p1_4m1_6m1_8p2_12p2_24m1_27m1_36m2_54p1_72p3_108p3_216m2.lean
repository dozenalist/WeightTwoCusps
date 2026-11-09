module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(3z) η(4z)^(-1) η(6z)^(-1) η(8z)^2 η(12z)^2 η(24z)^(-1) η(27z)^(-1) η(36z)^(-2) η(54z) η(72z)^3 η(108z)^3 η(216z)^(-2)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(4z)^(-1) η(6z)^(-1) η(8z)^2 η(12z)^2 η(24z)^(-1) η(27z)^(-1) η(36z)^(-2) η(54z) η(72z)^3 η(108z)^3 η(216z)^(-2)` at level 432. -/
abbrev cuspForm_432_eta_3p1_4m1_6m1_8p2_12p2_24m1_27m1_36m2_54p1_72p3_108p3_216m2 : gamma0CuspForms 432 :=
  etaQuotientCuspForm 432 sparse![432; 2 => 1, 3 => -1, 5 => -1, 7 => 2, 11 => 2, 23 => -1, 26 => -1, 35 => -2, 53 => 1, 71 => 3, 107 => 3, 215 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_432_eta_3p1_4m1_6m1_8p2_12p2_24m1_27m1_36m2_54p1_72p3_108p3_216m2_first_coeffs :
    first_coeffs 100 cuspForm_432_eta_3p1_4m1_6m1_8p2_12p2_24m1_27m1_36m2_54p1_72p3_108p3_216m2 =
    [0, 0, 0, 1, 0, 0, -1, 1, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, -1,
     0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, -1,
     0, 0, 0, 1, 0, 0, -3, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 1, 2, 0,
     0, 3, 0, 0, 2, 0, -2, -1, 0, 0, 1, 0, 0, -3, 0, -2, 1, 0, 2, 0,
     0, 0, -2, 0, 4, -1, 0, 0, 0, 0, 0, 0, 0, -5, 1, 0, 0, 1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
