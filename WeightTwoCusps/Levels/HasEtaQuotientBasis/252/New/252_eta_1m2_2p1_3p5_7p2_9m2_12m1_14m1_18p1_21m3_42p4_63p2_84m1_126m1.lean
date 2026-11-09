module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(7z)^2 η(9z)^(-2) η(12z)^(-1) η(14z)^(-1) η(18z) η(21z)^(-3) η(42z)^4 η(63z)^2 η(84z)^(-1) η(126z)^(-1)`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(7z)^2 η(9z)^(-2) η(12z)^(-1) η(14z)^(-1) η(18z) η(21z)^(-3) η(42z)^4 η(63z)^2 η(84z)^(-1) η(126z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p1_3p5_7p2_9m2_12m1_14m1_18p1_21m3_42p4_63p2_84m1_126m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 1, 2 => 5, 6 => 2, 8 => -2, 11 => -1, 13 => -1, 17 => 1, 20 => -3, 41 => 4, 62 => 2, 83 => -1, 125 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p1_3p5_7p2_9m2_12m1_14m1_18p1_21m3_42p4_63p2_84m1_126m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p1_3p5_7p2_9m2_12m1_14m1_18p1_21m3_42p4_63p2_84m1_126m1 =
    [0, 1, 2, 4, 3, 4, 4, 5, 2, -4, -2, 0, 4, -2, -2, 4, 9, 0, -8, -12,
     0, 0, -6, 0, 4, 19, 8, 4, 3, 0, -4, -4, -2, 8, -2, -4, 4, 6, -4, -20,
     -26, 0, 0, -8, -12, -8, 14, 8, -4, -11, -2, 0, 18, -8, 4, -8, -2, 4, -4, -12,
     -12, -14, 0, -4, -17, -16, -16, -8, 12, 0, 6, 8, -8, 22, -12, 4, -24, 0, 12, 28,
     -8, 8, -14, 4, -8, -32, -8, -16, 18, 8, 8, 14, 12, -8, -4, -8, 12, 6, 2, 0] := by
  eta_coeff

end WeightTwoCusps
