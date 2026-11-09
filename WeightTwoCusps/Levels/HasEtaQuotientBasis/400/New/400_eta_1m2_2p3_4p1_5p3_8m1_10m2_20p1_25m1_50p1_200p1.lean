module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-2) η(2z)^3 η(4z) η(5z)^3 η(8z)^(-1) η(10z)^(-2) η(20z) η(25z)^(-1) η(50z) η(200z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(4z) η(5z)^3 η(8z)^(-1) η(10z)^(-2) η(20z) η(25z)^(-1) η(50z) η(200z)` at level 400. -/
abbrev cuspForm_400_eta_1m2_2p3_4p1_5p3_8m1_10m2_20p1_25m1_50p1_200p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -2, 1 => 3, 3 => 1, 4 => 3, 7 => -1, 9 => -2, 19 => 1, 24 => -1, 49 => 1, 199 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m2_2p3_4p1_5p3_8m1_10m2_20p1_25m1_50p1_200p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m2_2p3_4p1_5p3_8m1_10m2_20p1_25m1_50p1_200p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 4, 4, 1, 2, 2, -2, 2,
     6, 0, 4, 6, -2, -1, 2, -2, -2, 4, 0, 0, 0, 0, -2, -3, 2, -2, 4, 0,
     0, 4, -2, -4, 2, 2, -4, 10, 0, -4, 1, -6, -2, -6, 0, 2, -4, -6, -2, -4,
     -12, 0, -4, 0, 2, 2, 0, -10, 6, -4, -4, 0, 0, -4, -6, -1, -6, 6, -4, 0,
     0, -8, -4, -10, -4, -4, 8, -2, 0, 4, -3, 4, -6, -2, -4, 4, -2, 6, 6, -4] := by
  eta_coeff

end WeightTwoCusps
