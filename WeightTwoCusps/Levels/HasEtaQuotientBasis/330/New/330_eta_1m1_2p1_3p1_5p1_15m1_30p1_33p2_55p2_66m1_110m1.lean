module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(30z) η(33z)^2 η(55z)^2 η(66z)^(-1) η(110z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(30z) η(33z)^2 η(55z)^2 η(66z)^(-1) η(110z)^(-1)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p1_3p1_5p1_15m1_30p1_33p2_55p2_66m1_110m1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 29 => 1, 32 => 2, 54 => 2, 65 => -1, 109 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p1_3p1_5p1_15m1_30p1_33p2_55p2_66m1_110m1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p1_3p1_5p1_15m1_30p1_33p2_55p2_66m1_110m1 =
    [0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 2, 1, 2,
     1, 0, 0, 2, 1, 1, 0, 1, 0, 0, 1, 2, 1, 0, 0, -2, -1, -2, 0, -2,
     1, -2, -2, -2, 0, -1, 2, 2, -1, -1, -3, 0, -4, 0, 1, 0, -6, -2, -4, -2,
     -3, 0, 2, -4, -5, -4, 0, -6, 2, 0, -2, -6, -3, -4, -4, -1, 2, 0, -6, -4,
     -5, -1, -4, 0, -4, 0, -8, -4, 0, 0, 1, 2, 6, 0, 2, -4, 5, 2, 5, 0] := by
  eta_coeff

end WeightTwoCusps
