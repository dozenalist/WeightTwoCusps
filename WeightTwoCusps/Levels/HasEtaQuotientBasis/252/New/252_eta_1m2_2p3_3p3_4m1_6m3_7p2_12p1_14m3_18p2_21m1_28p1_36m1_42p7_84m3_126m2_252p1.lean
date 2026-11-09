module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-3) η(7z)^2 η(12z) η(14z)^(-3) η(18z)^2 η(21z)^(-1) η(28z) η(36z)^(-1) η(42z)^7 η(84z)^(-3) η(126z)^(-2) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-3) η(7z)^2 η(12z) η(14z)^(-3) η(18z)^2 η(21z)^(-1) η(28z) η(36z)^(-1) η(42z)^7 η(84z)^(-3) η(126z)^(-2) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p3_3p3_4m1_6m3_7p2_12p1_14m3_18p2_21m1_28p1_36m1_42p7_84m3_126m2_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -3, 6 => 2, 11 => 1, 13 => -3, 17 => 2, 20 => -1, 27 => 1, 35 => -1, 41 => 7, 83 => -3, 125 => -2, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p3_3p3_4m1_6m3_7p2_12p1_14m3_18p2_21m1_28p1_36m1_42p7_84m3_126m2_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p3_3p3_4m1_6m3_7p2_12p1_14m3_18p2_21m1_28p1_36m1_42p7_84m3_126m2_252p1 =
    [0, 1, 2, 2, 1, 0, 2, 3, 2, 0, -2, 0, 2, 2, 2, 0, 1, 4, 4, 4,
     0, -2, 0, 0, -2, -1, 0, 2, 3, 0, 4, 8, 6, 4, -2, -4, 4, -2, -4, -4,
     -6, 4, 6, -4, -4, -4, 0, 8, -14, -19, -10, -8, 2, -8, -22, -4, -2, 0, 6, -12,
     -12, -6, -8, 0, 1, -16, 0, -8, -20, 4, -2, 0, 0, -30, -12, 6, -8, 4, -20, -16,
     8, 0, -2, 4, -10, 0, 16, -4, 8, 4, 0, 18, 12, 0, 16, 8, 22, 26, 2, 4] := by
  eta_coeff

end WeightTwoCusps
