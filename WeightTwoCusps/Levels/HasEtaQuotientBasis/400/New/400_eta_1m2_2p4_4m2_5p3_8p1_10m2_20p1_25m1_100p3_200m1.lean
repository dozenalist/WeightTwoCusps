module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-2) η(5z)^3 η(8z) η(10z)^(-2) η(20z) η(25z)^(-1) η(100z)^3 η(200z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-2) η(5z)^3 η(8z) η(10z)^(-2) η(20z) η(25z)^(-1) η(100z)^3 η(200z)^(-1)` at level 400. -/
abbrev cuspForm_400_eta_1m2_2p4_4m2_5p3_8p1_10m2_20p1_25m1_100p3_200m1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -2, 1 => 4, 3 => -2, 4 => 3, 7 => 1, 9 => -2, 19 => 1, 24 => -1, 99 => 3, 199 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m2_2p4_4m2_5p3_8p1_10m2_20p1_25m1_100p3_200m1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m2_2p4_4m2_5p3_8p1_10m2_20p1_25m1_100p3_200m1 =
    [0, 0, 0, 0, 1, 2, 1, 2, 4, 1, -1, 3, 2, -2, 2, 3, 1, 2, 2, 1,
     2, 0, -4, 0, -1, -1, 0, 0, 2, 2, 0, -4, 4, 2, -3, -1, 2, 0, -4, 2,
     0, 3, 2, -2, 1, 0, -2, -4, -4, -6, -1, -1, -6, 4, 3, -2, -2, 0, 2, -4,
     -4, 2, 4, -2, 1, 2, 1, 2, -2, 0, 4, -2, -8, -4, -2, -3, -7, -2, 4, 2,
     0, -6, 4, 6, -6, -8, 4, -2, -12, 7, 3, 6, 6, -2, -4, 4, -1, -8, -6, -8] := by
  eta_coeff

end WeightTwoCusps
