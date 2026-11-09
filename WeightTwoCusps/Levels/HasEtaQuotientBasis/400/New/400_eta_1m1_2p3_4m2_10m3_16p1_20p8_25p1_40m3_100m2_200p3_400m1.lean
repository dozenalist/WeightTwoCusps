module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-2) η(10z)^(-3) η(16z) η(20z)^8 η(25z) η(40z)^(-3) η(100z)^(-2) η(200z)^3 η(400z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-2) η(10z)^(-3) η(16z) η(20z)^8 η(25z) η(40z)^(-3) η(100z)^(-2) η(200z)^3 η(400z)^(-1)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p3_4m2_10m3_16p1_20p8_25p1_40m3_100m2_200p3_400m1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 3, 3 => -2, 9 => -3, 15 => 1, 19 => 8, 24 => 1, 39 => -3, 99 => -2, 199 => 3, 399 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p3_4m2_10m3_16p1_20p8_25p1_40m3_100m2_200p3_400m1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p3_4m2_10m3_16p1_20p8_25p1_40m3_100m2_200p3_400m1 =
    [0, 0, 1, 1, -1, 0, 1, 0, -1, -1, 2, 1, 1, 2, -1, 1, 0, -1, 0, -2,
     2, 1, -1, 0, 0, 1, -2, -1, 0, 0, -2, -3, -1, -1, 0, -3, 1, 2, -5, 1,
     0, -1, 0, -2, 2, -2, 1, 0, 1, 1, 0, 5, -2, -4, 0, 2, 0, -1, 6, 2,
     -4, -1, -6, 0, 0, -2, 0, 3, 1, 1, -2, -5, 2, -1, 2, -1, -2, -2, 4, 4,
     0, 1, 5, -1, 0, 4, -1, 0, 3, 2, -2, 3, 0, 4, 3, 4, 0, 4, -1, -3] := by
  eta_coeff

end WeightTwoCusps
