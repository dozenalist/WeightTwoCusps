module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(7z) η(9z)^(-1) η(12z)^2 η(14z)^(-2) η(18z)^2 η(21z)^(-3) η(28z) η(36z)^(-1) η(42z)^7 η(63z)^2 η(84z)^(-3) η(126z)^(-3) η(252z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(7z) η(9z)^(-1) η(12z)^2 η(14z)^(-2) η(18z)^2 η(21z)^(-3) η(28z) η(36z)^(-1) η(42z)^7 η(63z)^2 η(84z)^(-3) η(126z)^(-3) η(252z)^2` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p7_3p2_4m3_6m3_7p1_9m1_12p2_14m2_18p2_21m3_28p1_36m1_42p7_63p2_84m3_126m3_252p2 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 6 => 1, 8 => -1, 11 => 2, 13 => -2, 17 => 2, 20 => -3, 27 => 1, 35 => -1, 41 => 7, 62 => 2, 83 => -3, 125 => -3, 251 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p7_3p2_4m3_6m3_7p1_9m1_12p2_14m2_18p2_21m3_28p1_36m1_42p7_63p2_84m3_126m3_252p2_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p7_3p2_4m3_6m3_7p1_9m1_12p2_14m2_18p2_21m3_28p1_36m1_42p7_63p2_84m3_126m3_252p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, -1, -1, 1, 3, 0, -3, 1,
     2, 1, -2, -4, 2, 3, 0, 0, -1, -1, 1, 0, 5, 4, -6, -1, 2, 5, 2, -7,
     1, 6, 1, -3, -4, -2, 5, -2, -4, 0, -7, 0, -1, -1, 0, -8, 0, 5, 0, -2,
     -5, -7, 2, -2, -1, 5, -8, 0, -6, -6, 4, -5, -1, -2, -5, -2, 3, -2, 5, -5,
     -6, 3, -10, -2, -3, 2, 3, -2, -5, -2, 4, 4, 7, -2, -2, -3, 4, 16, 0, -2] := by
  eta_coeff

end WeightTwoCusps
