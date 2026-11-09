module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(14z) η(18z)^2 η(21z)^(-2) η(28z)^(-1) η(42z)^4 η(63z) η(126z)^(-2) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(14z) η(18z)^2 η(21z)^(-2) η(28z)^(-1) η(42z)^4 η(63z) η(126z)^(-2) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p2_3p5_6m3_9m2_14p1_18p2_21m2_28m1_42p4_63p1_126m2_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 13 => 1, 17 => 2, 20 => -2, 27 => -1, 41 => 4, 62 => 1, 125 => -2, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p2_3p5_6m3_9m2_14p1_18p2_21m2_28m1_42p4_63p1_126m2_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p2_3p5_6m3_9m2_14p1_18p2_21m2_28m1_42p4_63p1_126m2_252p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 1, -1, -1, 0, 3, 0, 1, -1, 1,
     3, 0, 1, -5, -2, -3, -1, 1, 0, 1, 1, 4, 2, -2, -4, 0, 4, 3, 1, -1,
     1, 5, 1, -1, -5, -3, -4, -4, -1, 0, -6, -8, -7, -1, 3, 0, -1, -5, 3, -1,
     1, -3, 0, 2, -1, 12, 6, 4, -4, -8, 0, -7, -3, -10, -4, 6, 7, -2, -9, -7,
     -3, -3, -2, 1, 0, 6, 6, 10, 2, 3, -3, 2, 5, 10, 0, 0, 2, 0, 0, -8] := by
  eta_coeff

end WeightTwoCusps
