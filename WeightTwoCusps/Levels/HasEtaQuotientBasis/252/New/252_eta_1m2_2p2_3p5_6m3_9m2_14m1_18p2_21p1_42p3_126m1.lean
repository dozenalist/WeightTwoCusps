module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(14z)^(-1) η(18z)^2 η(21z) η(42z)^3 η(126z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(14z)^(-1) η(18z)^2 η(21z) η(42z)^3 η(126z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p2_3p5_6m3_9m2_14m1_18p2_21p1_42p3_126m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 13 => -1, 17 => 2, 20 => 1, 41 => 3, 125 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p2_3p5_6m3_9m2_14m1_18p2_21p1_42p3_126m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p2_3p5_6m3_9m2_14m1_18p2_21p1_42p3_126m1 =
    [0, 1, 2, 3, 1, -1, -1, 0, 3, 0, 1, -1, 1, 3, 0, 3, -1, 4, -1, -3,
     -1, 0, 4, -5, -3, -3, 3, 5, 0, 1, 1, 6, 0, -8, -6, 1, 4, 0, -3, -1,
     5, 6, 0, -6, -7, -4, -6, -8, -1, 1, -6, -6, -9, 1, 5, 0, -1, -11, 4, -1,
     -1, -7, -4, 2, -3, 16, 4, 8, 0, -6, -1, -9, -3, -6, -10, 3, 9, -1, -3, -8,
     -3, -1, 2, 1, 0, 2, 4, 8, -4, 4, -2, 1, 9, 14, 6, 6, 3, -4, 2, -10] := by
  eta_coeff

end WeightTwoCusps
