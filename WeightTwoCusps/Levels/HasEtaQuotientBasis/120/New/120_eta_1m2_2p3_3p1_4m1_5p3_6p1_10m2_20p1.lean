module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z)^(-1) η(5z)^3 η(6z) η(10z)^(-2) η(20z)`; see
[the local level table](../../TABLE.md#level-120).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z)^(-1) η(5z)^3 η(6z) η(10z)^(-2) η(20z)` at level 120. -/
abbrev cuspForm_120_eta_1m2_2p3_3p1_4m1_5p3_6p1_10m2_20p1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -2, 1 => 3, 2 => 1, 3 => -1, 4 => 3, 5 => 1, 9 => -2, 19 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m2_2p3_3p1_4m1_5p3_6p1_10m2_20p1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m2_2p3_3p1_4m1_5p3_6p1_10m2_20p1 =
    [0, 1, 2, 2, 3, 4, 3, 0, 0, 1, -1, -2, 2, 4, -2, -1, -1, -4, -6, -4,
     -2, -6, -2, -2, -5, -7, 2, -4, -10, 0, -4, -4, -4, 2, 2, 0, 3, 0, -4, 2,
     5, -6, 2, 10, -2, 4, 4, 6, 6, -7, 2, -2, 4, 4, 7, 10, 10, 4, -2, 10,
     -3, 10, 4, 0, 11, -2, 2, 2, 16, 8, 2, 8, 0, -2, -2, 10, -8, 0, 8, -8,
     -6, 1, 4, -10, -10, 2, -8, -6, -10, 6, 7, 0, 0, -20, 0, -16, -1, 2, 2, -2] := by
  eta_coeff

end WeightTwoCusps
