module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(15z) η(22z) η(55z) η(110z)^(-1) η(330z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(15z) η(22z) η(55z) η(110z)^(-1) η(330z)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p2_3p1_6m1_15p1_22p1_55p1_110m1_330p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 14 => 1, 21 => 1, 54 => 1, 109 => -1, 329 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p2_3p1_6m1_15p1_22p1_55p1_110m1_330p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p2_3p1_6m1_15p1_22p1_55p1_110m1_330p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, 0,
     0, 0, -2, 0, 0, 0, 0, 0, -1, -2, 0, 0, 1, 0, 0, -1, -1, 2, 1, 1,
     0, 0, 0, -1, 2, 0, 0, 1, 0, 2, 1, 2, 2, -1, -1, 0, 0, -1, -1, -1,
     -1, 1, 1, 0, -2, 1, 2, 0, -2, -2, 0, -2, 2, 2, -2, 1, -1, 0, 0, -2,
     0, -3, -1, 1, 1, 0, 2, 0, 1, 1, 2, 0, -3, -3, -3, 0, -2, -1, 1, 0] := by
  eta_coeff

end WeightTwoCusps
