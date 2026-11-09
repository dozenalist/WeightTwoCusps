module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 100

The eta expression is `η(2z)^(-1) η(4z) η(10z)^6 η(20z)^(-2) η(50z)^(-1) η(100z)`; see
[the local level table](../../TABLE.md#level-100).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(10z)^6 η(20z)^(-2) η(50z)^(-1) η(100z)` at level 100. -/
abbrev cuspForm_100_eta_2m1_4p1_10p6_20m2_50m1_100p1 : gamma0CuspForms 100 :=
  etaQuotientCuspForm 100 sparse![100; 1 => -1, 3 => 1, 9 => 6, 19 => -2, 49 => -1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_100_eta_2m1_4p1_10p6_20m2_50m1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_100_eta_2m1_4p1_10p6_20m2_50m1_100p1 =
    [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, -3, 0, -2, 0, -1, 0, -6,
     0, -4, 0, 3, 0, -1, 0, -4, 0, 4, 0, -4, 0, -2, 0, 2, 0, 1, 0, 0,
     0, 6, 0, -1, 0, 1, 0, 9, 0, 0, 0, 10, 0, 5, 0, 0, 0, 2, 0, 8,
     0, 0, 0, -3, 0, 2, 0, -9, 0, -12, 0, -16, 0, 7, 0, 2, 0, -4, 0, 12,
     0, -8, 0, -7, 0, -6, 0, 2, 0, -14, 0, 8, 0, 0, 0, -4, 0, 1, 0, -4] := by
  eta_coeff

end WeightTwoCusps
