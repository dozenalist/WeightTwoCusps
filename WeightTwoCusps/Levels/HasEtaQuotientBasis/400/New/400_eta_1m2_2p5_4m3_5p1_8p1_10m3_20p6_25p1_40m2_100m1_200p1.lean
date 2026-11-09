module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(5z) η(8z) η(10z)^(-3) η(20z)^6 η(25z) η(40z)^(-2) η(100z)^(-1) η(200z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(5z) η(8z) η(10z)^(-3) η(20z)^6 η(25z) η(40z)^(-2) η(100z)^(-1) η(200z)` at level 400. -/
abbrev cuspForm_400_eta_1m2_2p5_4m3_5p1_8p1_10m3_20p6_25p1_40m2_100m1_200p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -2, 1 => 5, 3 => -3, 4 => 1, 7 => 1, 9 => -3, 19 => 6, 24 => 1, 39 => -2, 99 => -1, 199 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m2_2p5_4m3_5p1_8p1_10m3_20p6_25p1_40m2_100m1_200p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m2_2p5_4m3_5p1_8p1_10m3_20p6_25p1_40m2_100m1_200p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 1, -2, 0, 3, 1, 0, 4, 4, 3,
     2, 1, 2, 2, 0, -1, 3, 2, 2, 3, 0, 2, 0, 0, -1, -3, 0, 0, 2, -4,
     0, 3, -6, -2, 0, 2, -3, -2, 0, -1, 3, -5, 2, 4, -2, 2, 0, -4, -6, 2,
     -4, -4, 8, -6, 0, 2, -4, -4, -6, -5, -12, 0, 0, -4, -1, -1, 0, -4, -12, -6,
     0, -7, -2, 8, 0, -4, 1, -8, 0, 0, -9, -2, 6, -8, -5, 4, 0, -8, -2, 2] := by
  eta_coeff

end WeightTwoCusps
