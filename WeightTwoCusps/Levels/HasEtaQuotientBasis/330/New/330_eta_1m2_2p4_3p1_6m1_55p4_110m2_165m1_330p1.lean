module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(55z)^4 η(110z)^(-2) η(165z)^(-1) η(330z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(55z)^4 η(110z)^(-2) η(165z)^(-1) η(330z)` at level 330. -/
abbrev cuspForm_330_eta_1m2_2p4_3p1_6m1_55p4_110m2_165m1_330p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 54 => 4, 109 => -2, 164 => -1, 329 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m2_2p4_3p1_6m1_55p4_110m2_165m1_330p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m2_2p4_3p1_6m1_55p4_110m2_165m1_330p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, -1, 1, 0, 0, -2, -2, 1, -2,
     0, -1, -1, 0, -1, 0, -4, 0, 1, 0, 0, -2, 0, 0, 0, 2, 1, -2, 0, -1,
     0, 0, 1, 3, 0, 0, 2, 0, 0, 2, 0, -1, -1, 4, 0, 0, 0, 1, 2, 0,
     1, -2, -2, -7, -2, -4, 0, 4, -4, 0, 0, 8, 7, -3, 8, 0, 4, 4, -1, 6,
     0, 15, -2, -4, 1, 1, 8, 1, 0, -4, -8, -6, 8, 0, 0, 0, 0, -4, -10, 0] := by
  eta_coeff

end WeightTwoCusps
