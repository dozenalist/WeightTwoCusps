module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z) η(5z)^6 η(10z)^(-3) η(20z) η(25z)^(-1) η(100z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^6 η(10z)^(-3) η(20z) η(25z)^(-1) η(100z)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p1_5p6_10m3_20p1_25m1_100p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 1, 4 => 6, 9 => -3, 19 => 1, 24 => -1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p1_5p6_10m3_20p1_25m1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p1_5p6_10m3_20p1_25m1_100p1 =
    [0, 0, 0, 0, 1, 1, 1, 2, 2, -3, -2, -1, -6, -4, 4, 0, -3, 6, -2, -5,
     0, 0, -6, 2, 3, 1, 6, 6, 8, 0, 0, 2, 2, 2, 1, 4, -2, -4, -6, 4,
     0, -3, 8, -10, -3, -3, -4, -14, -2, 2, -2, -1, 4, 12, -7, -4, 6, -2, 8, -4,
     0, 4, -4, -2, -3, -2, -9, 12, -22, 4, 8, -4, -4, -2, 0, 0, 5, 0, 16, 14,
     0, 6, 6, 16, 2, 2, -2, -16, -6, 5, 6, 8, 24, -16, -6, -4, 3, -16, -4, -2] := by
  eta_coeff

end WeightTwoCusps
