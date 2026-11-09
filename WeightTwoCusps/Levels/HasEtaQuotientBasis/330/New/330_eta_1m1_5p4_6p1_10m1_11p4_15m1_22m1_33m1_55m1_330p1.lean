module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(5z)^4 η(6z) η(10z)^(-1) η(11z)^4 η(15z)^(-1) η(22z)^(-1) η(33z)^(-1) η(55z)^(-1) η(330z)`; see
[the local level table](../../TABLE.md#level-330).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(5z)^4 η(6z) η(10z)^(-1) η(11z)^4 η(15z)^(-1) η(22z)^(-1) η(33z)^(-1) η(55z)^(-1) η(330z)` at level 330. -/
abbrev cuspForm_330_eta_1m1_5p4_6p1_10m1_11p4_15m1_22m1_33m1_55m1_330p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 4 => 4, 5 => 1, 9 => -1, 10 => 4, 14 => -1, 21 => -1, 32 => -1, 54 => -1, 329 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_5p4_6p1_10m1_11p4_15m1_22m1_33m1_55m1_330p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_5p4_6p1_10m1_11p4_15m1_22m1_33m1_55m1_330p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 5, 3, 6, 6, 8,
     7, 12, 8, 11, 6, 6, 1, 11, 2, 8, 4, 11, -6, 3, -3, 10, 2, 7, -2, 4,
     -12, -12, -15, 2, -7, -6, -14, 0, -10, -12, -6, 4, 6, -10, -8, -5, -3, -18, -20, -3,
     -16, -16, -14, -2, -6, -12, -12, -15, -4, -16, -7, -5, -12, -12, -28, 0, 4, -6, 5, 10,
     8, -31, 24, 0, 16, -4, 13, -16, -10, -9, 0, 14, 16, -12, 12, -26, -8, -27, 6, 7] := by
  eta_coeff

end WeightTwoCusps
