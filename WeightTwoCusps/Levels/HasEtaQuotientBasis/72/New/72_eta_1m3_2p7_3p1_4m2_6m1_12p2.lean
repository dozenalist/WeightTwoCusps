module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 72

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(12z)^2`; see
[the local level table](../../TABLE.md#level-72).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(12z)^2` at level 72. -/
abbrev cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2 : gamma0CuspForms 72 :=
  etaQuotientCuspForm 72 sparse![72; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 11 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_first_coeffs :
    first_coeffs 100 cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2 =
    [0, 1, 3, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -2, -12, -4, 0, -1, 0, -4,
     0, 0, 0, 4, 0, -1, 6, 2, 0, -3, 0, 8, 0, 8, 0, 0, 0, 6, 24, -4,
     0, 3, 0, 4, 0, 4, 0, 0, 0, -7, -15, 4, 0, 1, 0, -8, 0, -8, 0, -2,
     0, -2, -12, 0, 0, -2, 0, -4, 0, -16, 0, -4, 0, 10, -30, -2, 0, 0, 0, -8,
     0, -2, 0, 2, 0, -4, 24, 12, 0, 3, 0, 0, 0, 16, 0, -4, 0, 2, 27, -8] := by
  eta_coeff

end WeightTwoCusps
