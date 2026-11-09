module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(2z)^2 η(4z)^(-1) η(6z)^(-1) η(12z)^2 η(18z)^3 η(24z)^(-1) η(36z)^(-2) η(48z) η(54z)^(-2) η(108z)^3 η(216z) η(432z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z)^2 η(4z)^(-1) η(6z)^(-1) η(12z)^2 η(18z)^3 η(24z)^(-1) η(36z)^(-2) η(48z) η(54z)^(-2) η(108z)^3 η(216z) η(432z)^(-1)` at level 432. -/
abbrev cuspForm_432_eta_2p2_4m1_6m1_12p2_18p3_24m1_36m2_48p1_54m2_108p3_216p1_432m1 : gamma0CuspForms 432 :=
  etaQuotientCuspForm 432 sparse![432; 1 => 2, 3 => -1, 5 => -1, 11 => 2, 17 => 3, 23 => -1, 35 => -2, 47 => 1, 53 => -2, 107 => 3, 215 => 1, 431 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_432_eta_2p2_4m1_6m1_12p2_18p3_24m1_36m2_48p1_54m2_108p3_216p1_432m1_first_coeffs :
    first_coeffs 100 cuspForm_432_eta_2p2_4m1_6m1_12p2_18p3_24m1_36m2_48p1_54m2_108p3_216p1_432m1 =
    [0, 1, 0, -2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -4,
     0, 4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 1, 0, -4, 0, 0, 0, 4, 0, 4,
     0, 0, 0, 4, 0, 0, 0, 0, 0, -4, 0, -2, 0, 0, 0, 1, 0, -12, 0, 0,
     0, 2, 0, 0, 0, 0, 0, 4, 0, 8, 0, 0, 0, 1, 0, 2, 0, 0, 0, -4,
     0, 0, 0, 0, 0, 2, 0, -6, 0, 0, 0, -8, 0, 12, 0, 0, 0, -1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
