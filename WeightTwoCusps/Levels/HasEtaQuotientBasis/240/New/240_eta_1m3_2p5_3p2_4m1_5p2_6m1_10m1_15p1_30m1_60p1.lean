module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^2 η(4z)^(-1) η(5z)^2 η(6z)^(-1) η(10z)^(-1) η(15z) η(30z)^(-1) η(60z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^2 η(4z)^(-1) η(5z)^2 η(6z)^(-1) η(10z)^(-1) η(15z) η(30z)^(-1) η(60z)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p5_3p2_4m1_5p2_6m1_10m1_15p1_30m1_60p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 5, 2 => 2, 3 => -1, 4 => 2, 5 => -1, 9 => -1, 14 => 1, 29 => -1, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p5_3p2_4m1_5p2_6m1_10m1_15p1_30m1_60p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p5_3p2_4m1_5p2_6m1_10m1_15p1_30m1_60p1 =
    [0, 0, 1, 3, 4, 5, 6, 6, 5, 4, 6, 6, 5, 6, 6, 4, 4, 6, 1, 0,
     -1, -2, -6, -8, 2, -4, -4, -1, -2, -6, -5, 0, -7, -2, -8, -6, -12, -6, 8, -8,
     -2, -4, -6, -8, -6, 1, -4, -4, -11, -4, -7, -8, 2, -14, -6, -10, -14, -12, -16, 6,
     -8, -8, -12, -2, -8, -12, 14, -12, 2, -12, -6, 4, 5, 12, -16, -1, -4, 0, -14, 8,
     11, -4, 18, -4, 6, 0, -4, 0, -6, 12, 6, -12, 8, 24, 16, 8, 14, 0, 17, 6] := by
  eta_coeff

end WeightTwoCusps
