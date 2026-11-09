module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(z) η(2z)^(-1) η(5z)^(-1) η(10z)^3 η(11z)^(-1) η(22z)^3 η(55z) η(110z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(5z)^(-1) η(10z)^3 η(11z)^(-1) η(22z)^3 η(55z) η(110z)^(-1)` at level 110. -/
abbrev cuspForm_110_eta_1p1_2m1_5m1_10p3_11m1_22p3_55p1_110m1 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 10 => -1, 21 => 3, 54 => 1, 109 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1p1_2m1_5m1_10p3_11m1_22p3_55p1_110m1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1p1_2m1_5m1_10p3_11m1_22p3_55p1_110m1 =
    [0, 1, -1, 0, -1, 1, 0, 0, -1, 1, -1, 0, 1, 1, 0, -1, 0, 2, -1, -1,
     0, -1, 0, -1, 3, 1, -1, -2, 2, 1, 1, -2, 0, 0, -2, -2, 0, 0, 1, -2,
     2, 2, 1, -1, 0, -2, 1, -2, 5, 0, -1, -3, 1, 1, 2, 0, 0, 1, -1, 1,
     -1, -1, 2, -1, -1, 5, 0, -1, -8, -3, 2, 2, -4, 3, 0, 0, 3, 0, 2, -2,
     -1, 5, -2, -3, -3, -2, 1, 1, 0, 6, 2, 2, -4, -4, 2, 1, 1, -1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
