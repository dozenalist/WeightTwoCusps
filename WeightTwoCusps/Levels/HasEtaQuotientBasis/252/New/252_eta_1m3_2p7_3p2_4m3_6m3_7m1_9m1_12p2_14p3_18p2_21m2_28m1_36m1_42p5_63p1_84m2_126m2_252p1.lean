module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(7z)^(-1) η(9z)^(-1) η(12z)^2 η(14z)^3 η(18z)^2 η(21z)^(-2) η(28z)^(-1) η(36z)^(-1) η(42z)^5 η(63z) η(84z)^(-2) η(126z)^(-2) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(7z)^(-1) η(9z)^(-1) η(12z)^2 η(14z)^3 η(18z)^2 η(21z)^(-2) η(28z)^(-1) η(36z)^(-1) η(42z)^5 η(63z) η(84z)^(-2) η(126z)^(-2) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p7_3p2_4m3_6m3_7m1_9m1_12p2_14p3_18p2_21m2_28m1_36m1_42p5_63p1_84m2_126m2_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 6 => -1, 8 => -1, 11 => 2, 13 => 3, 17 => 2, 20 => -2, 27 => -1, 35 => -1, 41 => 5, 62 => 1, 83 => -2, 125 => -2, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p7_3p2_4m3_6m3_7m1_9m1_12p2_14p3_18p2_21m2_28m1_36m1_42p5_63p1_84m2_126m2_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p7_3p2_4m3_6m3_7m1_9m1_12p2_14p3_18p2_21m2_28m1_36m1_42p5_63p1_84m2_126m2_252p1 =
    [0, 0, 0, 1, 3, 2, -1, -1, 1, 3, 2, 3, 5, 0, -1, 0, 2, 2, -3, 2,
     4, 1, -5, -7, 3, 8, 2, -5, -2, -1, 4, 2, 6, 8, -8, -2, 3, 10, 0, -12,
     0, 8, 3, -12, -9, -4, 7, -6, -11, 0, -10, -2, -6, -3, -7, -18, -2, 10, 5, -8,
     -12, -18, 2, -1, -1, 10, -16, 4, -8, -8, 4, -7, 1, -6, -12, -5, 10, -3, 8, -20,
     -6, 9, -18, 2, -7, 8, 6, -6, -7, 4, 8, 10, 13, -4, 6, -6, 11, 42, 0, 0] := by
  eta_coeff

end WeightTwoCusps
