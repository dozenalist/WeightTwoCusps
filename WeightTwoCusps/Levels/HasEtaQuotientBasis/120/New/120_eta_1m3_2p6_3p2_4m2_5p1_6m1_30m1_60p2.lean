module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z) η(6z)^(-1) η(30z)^(-1) η(60z)^2`; see
[the local level table](../../TABLE.md#level-120).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z) η(6z)^(-1) η(30z)^(-1) η(60z)^2` at level 120. -/
abbrev cuspForm_120_eta_1m3_2p6_3p2_4m2_5p1_6m1_30m1_60p2 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 1, 5 => -1, 29 => -1, 59 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m3_2p6_3p2_4m2_5p1_6m1_30m1_60p2_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m3_2p6_3p2_4m2_5p1_6m1_30m1_60p2 =
    [0, 0, 0, 0, 1, 3, 3, 2, 2, 2, 1, -2, 0, 2, -2, -3, -3, -2, -4, -4,
     0, 0, -2, -4, -3, -8, -2, 0, -2, 2, -4, 4, -2, -2, 6, 2, 1, -2, 4, 2,
     3, 0, 6, 8, -2, 5, -4, 0, 4, -8, 0, -2, 0, -2, -1, 10, 2, 0, -6, 6,
     -1, 4, 4, -6, 9, -4, 2, -4, 4, 2, 2, 4, 2, 4, -6, 8, 0, 8, 8, -4,
     -4, -4, 0, 4, -2, 4, 8, -2, -10, 4, 5, -4, 0, -4, 8, -16, 1, 8, 0, 6] := by
  eta_coeff

end WeightTwoCusps
