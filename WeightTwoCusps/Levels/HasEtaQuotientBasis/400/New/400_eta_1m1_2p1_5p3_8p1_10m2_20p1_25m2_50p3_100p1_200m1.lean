module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(8z) η(10z)^(-2) η(20z) η(25z)^(-2) η(50z)^3 η(100z) η(200z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(8z) η(10z)^(-2) η(20z) η(25z)^(-2) η(50z)^3 η(100z) η(200z)^(-1)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p1_5p3_8p1_10m2_20p1_25m2_50p3_100p1_200m1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 1, 4 => 3, 7 => 1, 9 => -2, 19 => 1, 24 => -2, 49 => 3, 99 => 1, 199 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p1_5p3_8p1_10m2_20p1_25m2_50p3_100p1_200m1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p1_5p3_8p1_10m2_20p1_25m2_50p3_100p1_200m1 =
    [0, 1, 1, 1, 2, 2, 0, 1, 2, -1, 1, 2, 0, 0, 4, 1, 0, 2, -1, -2,
     -2, 0, 0, 1, 0, 1, 2, 0, 2, 2, 0, 0, 2, 2, -2, 5, 2, -2, 0, 4,
     0, 0, 2, -3, 0, -4, -4, -1, -2, -3, 1, -2, -2, 2, 0, -6, 0, 0, 0, -4,
     4, 2, -4, -3, 0, -2, 0, 1, -4, 0, -4, -4, -4, -4, -6, -1, -8, 2, 4, 4,
     0, -3, -2, 3, -8, 0, 8, -4, -6, 8, -3, 4, 6, -6, -4, -4, 0, -8, 3, -4] := by
  eta_coeff

end WeightTwoCusps
