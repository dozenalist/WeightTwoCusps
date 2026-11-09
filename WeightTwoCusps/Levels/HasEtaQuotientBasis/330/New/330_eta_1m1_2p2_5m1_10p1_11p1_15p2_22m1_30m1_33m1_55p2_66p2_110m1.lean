module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z)^2 η(5z)^(-1) η(10z) η(11z) η(15z)^2 η(22z)^(-1) η(30z)^(-1) η(33z)^(-1) η(55z)^2 η(66z)^2 η(110z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(5z)^(-1) η(10z) η(11z) η(15z)^2 η(22z)^(-1) η(30z)^(-1) η(33z)^(-1) η(55z)^2 η(66z)^2 η(110z)^(-1)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p2_5m1_10p1_11p1_15p2_22m1_30m1_33m1_55p2_66p2_110m1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 2, 4 => -1, 9 => 1, 10 => 1, 14 => 2, 21 => -1, 29 => -1, 32 => -1, 54 => 2, 65 => 2, 109 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p2_5m1_10p1_11p1_15p2_22m1_30m1_33m1_55p2_66p2_110m1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p2_5m1_10p1_11p1_15p2_22m1_30m1_33m1_55p2_66p2_110m1 =
    [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, -1, 1, -1, 2,
     0, -2, 0, -1, 2, -1, -2, 0, -1, 2, 0, -1, 2, 0, 0, 0, -1, 1, 0, 2,
     0, -2, 2, -2, 1, 2, -2, 0, -1, 2, 0, -2, 0, -2, 2, -1, -2, 1, 0, -1,
     -4, -2, -3, 0, -1, -6, 0, -1, -1, -5, -4, 1, -3, 2, -4, -1, 2, 0, 0, -4,
     2, 2, 2, 2, -4, -2, 0, -5, 0, 1, -4, 0, 0, -1, -4, -1, 2, -5, 5, -3] := by
  eta_coeff

end WeightTwoCusps
