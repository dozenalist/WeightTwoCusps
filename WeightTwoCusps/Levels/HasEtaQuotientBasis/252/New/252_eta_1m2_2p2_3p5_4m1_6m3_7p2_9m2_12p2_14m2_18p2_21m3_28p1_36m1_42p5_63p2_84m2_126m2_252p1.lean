module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(4z)^(-1) η(6z)^(-3) η(7z)^2 η(9z)^(-2) η(12z)^2 η(14z)^(-2) η(18z)^2 η(21z)^(-3) η(28z) η(36z)^(-1) η(42z)^5 η(63z)^2 η(84z)^(-2) η(126z)^(-2) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(4z)^(-1) η(6z)^(-3) η(7z)^2 η(9z)^(-2) η(12z)^2 η(14z)^(-2) η(18z)^2 η(21z)^(-3) η(28z) η(36z)^(-1) η(42z)^5 η(63z)^2 η(84z)^(-2) η(126z)^(-2) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p2_3p5_4m1_6m3_7p2_9m2_12p2_14m2_18p2_21m3_28p1_36m1_42p5_63p2_84m2_126m2_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 2, 2 => 5, 3 => -1, 5 => -3, 6 => 2, 8 => -2, 11 => 2, 13 => -2, 17 => 2, 20 => -3, 27 => 1, 35 => -1, 41 => 5, 62 => 2, 83 => -2, 125 => -2, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p2_3p5_4m1_6m3_7p2_9m2_12p2_14m2_18p2_21m3_28p1_36m1_42p5_63p2_84m2_126m2_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p2_3p5_4m1_6m3_7p2_9m2_12p2_14m2_18p2_21m3_28p1_36m1_42p5_63p2_84m2_126m2_252p1 =
    [0, 0, 0, 0, 0, 1, 2, 3, 1, 0, 1, 3, 2, -3, -2, 3, 6, 0, -5, -3,
     5, 1, -4, -5, 2, 8, 1, 0, 1, 1, -1, -2, 2, 6, -4, -3, 4, 8, 3, -11,
     -11, 6, 1, -2, -11, -4, 8, 4, -4, -6, -8, -2, 7, -7, 2, -10, -1, 5, -2, -7,
     -7, -11, 4, -2, -6, 0, -8, -4, 4, -8, 5, -5, -5, 6, -6, 2, -9, -1, 3, 10,
     -13, 3, -12, 3, -5, -10, 0, -2, 8, 4, 4, 9, 9, -2, -6, -2, 8, 12, 0, -4] := by
  eta_coeff

end WeightTwoCusps
