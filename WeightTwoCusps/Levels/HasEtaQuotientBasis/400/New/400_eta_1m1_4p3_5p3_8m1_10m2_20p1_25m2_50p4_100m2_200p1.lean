module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(4z)^3 η(5z)^3 η(8z)^(-1) η(10z)^(-2) η(20z) η(25z)^(-2) η(50z)^4 η(100z)^(-2) η(200z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(4z)^3 η(5z)^3 η(8z)^(-1) η(10z)^(-2) η(20z) η(25z)^(-2) η(50z)^4 η(100z)^(-2) η(200z)` at level 400. -/
abbrev cuspForm_400_eta_1m1_4p3_5p3_8m1_10m2_20p1_25m2_50p4_100m2_200p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 3 => 3, 4 => 3, 7 => -1, 9 => -2, 19 => 1, 24 => -2, 49 => 4, 99 => -2, 199 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_4p3_5p3_8m1_10m2_20p1_25m2_50p4_100m2_200p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_4p3_5p3_8m1_10m2_20p1_25m2_50p4_100m2_200p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 2, 1, 2, 0, -1, 4, 1, 1, 4,
     2, -2, 3, 1, -4, 1, 0, -1, 0, 4, 0, -2, 1, -1, 0, 3, 4, 2, 3, 2,
     0, 6, -4, 3, 4, -2, 0, 5, -1, -6, 3, -6, -2, -2, 0, -2, -8, -3, -4, -8,
     -4, 2, 2, -5, 4, -2, 0, -10, 1, -6, -12, 6, -2, -3, 0, 1, -12, -4, -8, -4,
     0, -10, -3, 0, -8, 4, 0, 0, -3, 0, -9, 2, 0, 0, 0, -4, -4, 0, 2, -6] := by
  eta_coeff

end WeightTwoCusps
