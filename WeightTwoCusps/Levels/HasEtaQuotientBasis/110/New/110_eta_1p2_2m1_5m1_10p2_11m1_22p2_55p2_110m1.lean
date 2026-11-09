module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(z)^2 η(2z)^(-1) η(5z)^(-1) η(10z)^2 η(11z)^(-1) η(22z)^2 η(55z)^2 η(110z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(5z)^(-1) η(10z)^2 η(11z)^(-1) η(22z)^2 η(55z)^2 η(110z)^(-1)` at level 110. -/
abbrev cuspForm_110_eta_1p2_2m1_5m1_10p2_11m1_22p2_55p2_110m1 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 10 => -1, 21 => 2, 54 => 2, 109 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1p2_2m1_5m1_10p2_11m1_22p2_55p2_110m1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1p2_2m1_5m1_10p2_11m1_22p2_55p2_110m1 =
    [0, 0, 1, -2, 0, 0, 2, 1, -2, 0, 0, 0, 0, 1, -2, 0, -2, 3, 1, -2,
     0, 2, 0, 2, 0, 0, -2, -4, 1, 0, 0, 0, 1, 0, 2, 1, 0, -2, 0, 2,
     1, -4, -2, 1, 0, 0, 0, 2, 2, 0, 1, -2, -1, -2, 4, 0, 2, -4, 4, 0,
     -2, -6, -4, 5, 0, -1, 0, 0, 1, 4, 0, 8, -6, -1, 0, -2, -2, -1, -6, 4,
     0, 8, 8, -3, -2, 1, -2, 0, -1, -4, -4, 0, 4, 0, -8, -2, 10, 2, -5, 0] := by
  eta_coeff

end WeightTwoCusps
