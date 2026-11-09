module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(z)^3 η(2z)^(-1) η(5z)^(-1) η(10z) η(11z)^(-1) η(22z) η(55z)^3 η(110z)^(-1)`; see
[the local level table](../../TABLE.md#level-110).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-1) η(5z)^(-1) η(10z) η(11z)^(-1) η(22z) η(55z)^3 η(110z)^(-1)` at level 110. -/
abbrev cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 10 => -1, 21 => 1, 54 => 3, 109 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1 =
    [0, 0, 0, 1, -3, 1, 2, 2, 0, -7, 2, 0, 2, 2, -2, -2, 3, 2, 4, -6,
     -7, 4, 0, 3, -4, 0, -2, 5, 4, 4, -4, -5, 6, 1, -8, -4, 1, -3, 6, 0,
     8, -2, -10, 8, 1, -3, 0, -2, 0, 2, 0, 12, -6, -10, 4, 1, -2, -6, 2, -1,
     4, 0, 8, -2, 3, 2, 2, -15, -8, 3, -2, 1, -2, 10, 12, 1, 2, 2, -12, 2,
     -3, 0, -4, -4, 2, 4, -8, -2, 0, 13, 0, 0, -4, 1, 2, -2, 0, 5, -2, 1] := by
  eta_coeff

end WeightTwoCusps
