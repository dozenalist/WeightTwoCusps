module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 80

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(5z)^(-2) η(10z)^5 η(20z)^(-1)`; see
[the local level table](../../TABLE.md#level-80).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(5z)^(-2) η(10z)^5 η(20z)^(-1)` at level 80. -/
abbrev cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1 : gamma0CuspForms 80 :=
  etaQuotientCuspForm 80 sparse![80; 0 => -2, 1 => 5, 3 => -1, 4 => -2, 9 => 5, 19 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1 =
    [0, 1, 2, 0, 0, 1, 0, 4, 0, -3, 2, -4, 0, -2, -8, 0, 0, 2, -6, -4,
     0, 0, 8, -4, 0, 1, -4, 0, 0, -2, 0, 8, 0, 0, 4, 4, 0, 6, 8, 0,
     0, -6, 0, 8, 0, -3, 8, -4, 0, 9, 2, 0, 0, 6, 0, -4, 0, 0, -4, 4,
     0, -2, -16, -12, 0, -2, 0, -8, 0, 0, -8, 0, 0, -6, 12, 0, 0, -16, 0, 0,
     0, 9, -12, 16, 0, 2, -16, 0, 0, -6, -6, -8, 0, 0, 8, -4, 0, -14, 18, 12] := by
  eta_coeff

end WeightTwoCusps
