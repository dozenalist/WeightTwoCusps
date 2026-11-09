module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z) η(15z)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z) η(15z)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p6_3p1_4m2_5p1_15p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 1, 14 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p6_3p1_4m2_5p1_15p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p6_3p1_4m2_5p1_15p1 =
    [0, 1, 3, 3, 3, 5, 5, 4, 3, 5, 7, 4, 5, 6, 4, 3, 3, 2, 3, 4,
     -1, 0, -4, 0, 1, -7, 2, -1, 0, -2, -3, 0, -5, -8, -10, -4, -13, -2, -4, -10,
     -1, -10, -8, -16, -4, 1, -12, -8, -7, -11, -13, -2, 2, -6, -7, -8, -8, -8, -6, -4,
     -7, 2, -8, -4, -5, -6, 4, -8, -2, -8, -4, -8, 3, 10, -6, -5, -4, 0, -2, 16,
     7, -3, -2, 8, 8, -2, 16, 6, -4, 10, 7, -8, 8, 12, 20, 12, 9, 2, -5, 4] := by
  eta_coeff

end WeightTwoCusps
