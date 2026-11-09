module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-3) η(8z)^3 η(10z)^(-3) η(16z)^(-1) η(20z)^8 η(25z) η(40z)^(-3) η(100z)^(-1) η(400z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-3) η(8z)^3 η(10z)^(-3) η(16z)^(-1) η(20z)^8 η(25z) η(40z)^(-3) η(100z)^(-1) η(400z)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p3_4m3_8p3_10m3_16m1_20p8_25p1_40m3_100m1_400p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 3, 3 => -3, 7 => 3, 9 => -3, 15 => -1, 19 => 8, 24 => 1, 39 => -3, 99 => -1, 399 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p3_4m3_8p3_10m3_16m1_20p8_25p1_40m3_100m1_400p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p3_4m3_8p3_10m3_16m1_20p8_25p1_40m3_100m1_400p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 2, 1,
     -2, -1, 2, 0, 1, 1, 0, 2, 2, 2, -2, -1, 0, -2, 1, -3, 1, 2, -2, 1,
     0, 2, -6, -4, 1, -2, -1, -6, 0, 1, -2, 0, -2, 0, -3, 2, 2, -2, 2, -2,
     4, -1, 0, 2, -1, -2, -1, 8, -4, -5, 6, 3, 0, 2, -2, -1, -3, -4, -8, -2,
     0, -3, 4, 4, -2, 4, 3, -4, 0, -5, 4, -1, 6, 2, 3, 4, 1, 4, -2, -1] := by
  eta_coeff

end WeightTwoCusps
