module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(6z)^(-1) η(11z)^(-1) η(15z) η(22z) η(33z)^2 η(66z)^(-1) η(165z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(6z)^(-1) η(11z)^(-1) η(15z) η(22z) η(33z)^2 η(66z)^(-1) η(165z)` at level 330. -/
abbrev cuspForm_330_eta_1m1_2p1_3p2_6m1_11m1_15p1_22p1_33p2_66m1_165p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 10 => -1, 14 => 1, 21 => 1, 32 => 2, 65 => -1, 164 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m1_2p1_3p2_6m1_11m1_15p1_22p1_33p2_66m1_165p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m1_2p1_3p2_6m1_11m1_15p1_22p1_33p2_66m1_165p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1,
     2, 1, 0, 0, 0, -1, 1, 0, -1, 0, 1, 2, 1, 0, 1, -1, -1, 1, -2, -2,
     -1, 0, 1, 0, 0, -1, -2, -1, 1, -3, -3, -1, 0, -1, 0, 0, -1, -1, -1, 2,
     -4, -2, -1, 0, -1, 2, 0, -2, 1, -1, 3, -2, -1, -1, -2, -1, 1, 0, 0, -1,
     -3, 1, -1, 0, 0, 1, 0, 2, 1, 0, 1, -1, 1, -3, 0, -1, 1, 1, 1, 1] := by
  eta_coeff

end WeightTwoCusps
