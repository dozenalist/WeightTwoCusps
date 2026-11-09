module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(10z)^3 η(20z) η(25z) η(50z)^(-1)`; see
[the local level table](../../TABLE.md#level-200).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(10z)^3 η(20z) η(25z) η(50z)^(-1)` at level 200. -/
abbrev cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 0 => -1, 1 => 2, 3 => -1, 9 => 3, 19 => 1, 24 => 1, 49 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1 =
    [0, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, -1, -1, 3, 0, 0, 1, 2, 2, -1,
     0, 0, 1, -1, -1, 1, -2, -5, -2, -2, -4, 2, 1, -5, 1, -4, -2, 1, -7, 0,
     0, -1, -6, -3, -3, -3, 0, -1, -1, -1, -2, -5, 4, 1, -3, 4, -2, -5, 8, -4,
     0, -2, -6, 7, 1, -2, -1, 8, 3, 0, 4, 0, -2, 4, 0, 0, 5, -6, -4, 10,
     0, -1, 9, -6, 2, 2, 2, 10, -3, -1, 2, 8, -6, -10, 6, 4, -1, 1, -3, -2] := by
  eta_coeff

end WeightTwoCusps
