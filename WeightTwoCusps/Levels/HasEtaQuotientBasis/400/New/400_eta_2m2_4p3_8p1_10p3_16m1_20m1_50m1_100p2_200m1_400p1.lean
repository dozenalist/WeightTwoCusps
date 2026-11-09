module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(2z)^(-2) η(4z)^3 η(8z) η(10z)^3 η(16z)^(-1) η(20z)^(-1) η(50z)^(-1) η(100z)^2 η(200z)^(-1) η(400z)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^3 η(8z) η(10z)^3 η(16z)^(-1) η(20z)^(-1) η(50z)^(-1) η(100z)^2 η(200z)^(-1) η(400z)` at level 400. -/
abbrev cuspForm_400_eta_2m2_4p3_8p1_10p3_16m1_20m1_50m1_100p2_200m1_400p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 1 => -2, 3 => 3, 7 => 1, 9 => 3, 15 => -1, 19 => -1, 49 => -1, 99 => 2, 199 => -1, 399 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_2m2_4p3_8p1_10p3_16m1_20m1_50m1_100p2_200m1_400p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_2m2_4p3_8p1_10p3_16m1_20m1_50m1_100p2_200m1_400p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2,
     0, 4, 0, 4, 0, 1, 0, 2, 0, 2, 0, -2, 0, 2, 0, 5, 0, -2, 0, 2,
     0, 2, 0, -6, 0, -2, 0, 0, 0, -4, 0, 0, 0, 2, 0, -6, 0, 0, 0, -4,
     0, -6, 0, 0, 0, -2, 0, 0, 0, 0, 0, 6, 0, -4, 0, -1, 0, 2, 0, -4,
     0, -8, 0, 0, 0, 4, 0, -8, 0, 10, 0, -2, 0, -6, 0, -4, 0, -8, 0, -2] := by
  eta_coeff

end WeightTwoCusps
