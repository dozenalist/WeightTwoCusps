module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(7z)^(-2) η(12z) η(14z)^5 η(28z)^(-2) η(42z)^(-1) η(63z)^2 η(84z) η(126z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(7z)^(-2) η(12z) η(14z)^5 η(28z)^(-2) η(42z)^(-1) η(63z)^2 η(84z) η(126z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p7_3p1_4m2_6m2_7m2_12p1_14p5_28m2_42m1_63p2_84p1_126m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 6 => -2, 11 => 1, 13 => 5, 27 => -2, 41 => -1, 62 => 2, 83 => 1, 125 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p7_3p1_4m2_6m2_7m2_12p1_14p5_28m2_42m1_63p2_84p1_126m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p7_3p1_4m2_6m2_7m2_12p1_14p5_28m2_42m1_63p2_84p1_126m1 =
    [0, 0, 1, 3, 2, 0, 1, 0, 1, 5, 6, 4, -1, 2, 1, -1, 6, 0, 0, -2,
     -2, 2, -8, 0, 1, 0, -2, -7, 0, -4, 1, 8, 3, -10, -4, 0, 1, 4, 0, 1,
     -18, 0, 2, -8, 2, 0, 8, -8, -3, 0, -5, 4, 2, 4, -5, -4, 1, -5, 0, 0,
     -1, -14, -4, 5, -10, 4, 0, 8, -10, -8, 6, -4, 0, -12, -2, -13, -2, 0, -7, -12,
     2, 10, -20, 0, -2, 4, 8, 4, 16, -8, 0, 6, 2, 10, -12, -4, 3, 8, 1, -8] := by
  eta_coeff

end WeightTwoCusps
