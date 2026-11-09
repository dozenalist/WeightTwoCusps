module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(7z) η(9z)^(-1) η(12z) η(14z)^(-1) η(18z) η(21z)^(-2) η(42z)^3 η(63z)^2 η(126z)^(-2) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(7z) η(9z)^(-1) η(12z) η(14z)^(-1) η(18z) η(21z)^(-2) η(42z)^3 η(63z)^2 η(126z)^(-2) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_7p1_9m1_12p1_14m1_18p1_21m2_42p3_63p2_126m2_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 6 => 1, 8 => -1, 11 => 1, 13 => -1, 17 => 1, 20 => -2, 41 => 3, 62 => 2, 125 => -2, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_7p1_9m1_12p1_14m1_18p1_21m2_42p3_63p2_126m2_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_7p1_9m1_12p1_14m1_18p1_21m2_42p3_63p2_126m2_252p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 1, -1, 0, 3, 1, -1, -2, -1,
     3, 0, -1, -2, -2, 2, -1, -1, 0, -1, 1, 2, 1, 2, -2, -1, 5, 2, 1, -5,
     -3, 3, 1, -2, -4, -3, -1, 0, -3, 0, -3, -4, -3, -1, 3, 0, -1, -1, 1, -1,
     -3, -3, 0, 1, -2, 1, 2, 0, -2, -4, 1, -3, -4, -4, -1, 6, 3, -1, -5, 0,
     -1, 0, -4, -1, -2, -2, 3, 2, 5, -3, -1, 3, 3, 2, -4, -3, 6, 2, 0, -4] := by
  eta_coeff

end WeightTwoCusps
