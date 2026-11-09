module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z)^(-1) η(6z)^4 η(7z)^2 η(12z)^(-2) η(14z)^(-3) η(18z)^(-2) η(21z)^(-3) η(28z) η(36z) η(42z)^6 η(84z)^(-2) η(126z)^2 η(252z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z)^(-1) η(6z)^4 η(7z)^2 η(12z)^(-2) η(14z)^(-3) η(18z)^(-2) η(21z)^(-3) η(28z) η(36z) η(42z)^6 η(84z)^(-2) η(126z)^2 η(252z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p3_3p1_4m1_6p4_7p2_12m2_14m3_18m2_21m3_28p1_36p1_42p6_84m2_126p2_252m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 3, 2 => 1, 3 => -1, 5 => 4, 6 => 2, 11 => -2, 13 => -3, 17 => -2, 20 => -3, 27 => 1, 35 => 1, 41 => 6, 83 => -2, 125 => 2, 251 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p3_3p1_4m1_6p4_7p2_12m2_14m3_18m2_21m3_28p1_36p1_42p6_84m2_126p2_252m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p3_3p1_4m1_6p4_7p2_12m2_14m3_18m2_21m3_28p1_36p1_42p6_84m2_126p2_252m1 =
    [0, 1, 2, 2, 3, 4, 6, 3, -2, 0, -2, -4, -10, -10, 2, 0, -1, 0, 4, 16,
     8, -2, 4, 4, 10, -1, -16, 2, 1, 0, -4, -16, 2, 4, -6, 0, -12, -2, 12, -4,
     2, -8, 2, 20, -4, -4, -4, 0, 6, -19, -10, -8, -6, 0, -18, -4, 2, 0, 6, -4,
     12, 30, -8, 0, -5, -8, 0, -32, -12, 4, -2, 12, 8, -6, 20, 6, 4, 0, -12, 8,
     0, 0, 2, 4, 2, 0, 16, -4, -4, 8, 0, 6, -4, 0, 16, -8, -14, 26, 2, 4] := by
  eta_coeff

end WeightTwoCusps
