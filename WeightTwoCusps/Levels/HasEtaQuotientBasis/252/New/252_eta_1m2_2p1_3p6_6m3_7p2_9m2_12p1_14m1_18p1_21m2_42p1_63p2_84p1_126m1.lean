module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-3) η(7z)^2 η(9z)^(-2) η(12z) η(14z)^(-1) η(18z) η(21z)^(-2) η(42z) η(63z)^2 η(84z) η(126z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-3) η(7z)^2 η(9z)^(-2) η(12z) η(14z)^(-1) η(18z) η(21z)^(-2) η(42z) η(63z)^2 η(84z) η(126z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p1_3p6_6m3_7p2_9m2_12p1_14m1_18p1_21m2_42p1_63p2_84p1_126m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 1, 2 => 6, 5 => -3, 6 => 2, 8 => -2, 11 => 1, 13 => -1, 17 => 1, 20 => -2, 41 => 1, 62 => 2, 83 => 1, 125 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p1_3p6_6m3_7p2_9m2_12p1_14m1_18p1_21m2_42p1_63p2_84p1_126m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p1_3p6_6m3_7p2_9m2_12p1_14m1_18p1_21m2_42p1_63p2_84p1_126m1 =
    [0, 0, 0, 0, 1, 2, 4, 2, 2, 0, 4, 2, 0, -4, 0, 4, 5, -2, -4, -2,
     0, 0, -8, -2, 0, 6, 4, 0, 1, 0, -4, 0, -2, 4, 0, -2, 4, 6, -4, -8,
     -18, 2, 0, -2, -4, -4, 8, 4, 0, -6, 0, -4, 6, -4, 4, -2, -2, 0, 0, -4,
     -4, -4, 0, 0, -5, -4, 0, -2, 4, -4, 4, 2, -8, 0, -8, 8, -8, -2, -4, 6,
     0, 0, -16, 0, -4, -6, 0, 0, 18, 2, 0, 8, 4, 0, -8, -8, 8, 4, 0, -4] := by
  eta_coeff

end WeightTwoCusps
