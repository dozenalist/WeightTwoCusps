module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(4z) η(5z)^6 η(10z)^(-3) η(20z) η(25z)^(-1) η(50z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(4z) η(5z)^6 η(10z)^(-3) η(20z) η(25z)^(-1) η(50z)` at level 400. -/
abbrev cuspForm_400_eta_1m1_4p1_5p6_10m3_20p1_25m1_50p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 3 => 1, 4 => 6, 9 => -3, 19 => 1, 24 => -1, 49 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_4p1_5p6_10m3_20p1_25m1_50p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_4p1_5p6_10m3_20p1_25m1_50p1 =
    [0, 0, 1, 1, 2, 3, 4, 0, 3, 0, -2, -2, 5, -4, 2, 4, -2, -5, 4, -6,
     -8, -2, -5, -8, 2, -1, 2, -3, -2, -6, 0, -4, 3, 3, -4, 0, 0, 2, -5, 8,
     0, -6, 2, 6, -2, -1, -2, -6, -3, 2, -2, 10, -8, 2, 2, -4, 4, 11, 0, -4,
     16, 8, 6, 2, -2, 2, -6, 11, 9, 10, 8, 0, -6, 1, 6, -4, -2, -2, 4, 12,
     0, 14, 3, 3, -4, -10, -6, 12, -9, 0, 6, 4, -6, 10, -10, 4, 2, -6, -7, -4] := by
  eta_coeff

end WeightTwoCusps
