module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-2) η(14z)^2 η(18z) η(21z)^(-1) η(28z)^(-1) η(42z) η(63z) η(126z)^(-1) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-2) η(14z)^2 η(18z) η(21z)^(-1) η(28z)^(-1) η(42z) η(63z) η(126z)^(-1) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p1_3p6_6m2_9m2_14p2_18p1_21m1_28m1_42p1_63p1_126m1_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 13 => 2, 17 => 1, 20 => -1, 27 => -1, 41 => 1, 62 => 1, 125 => -1, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p1_3p6_6m2_9m2_14p2_18p1_21m1_28m1_42p1_63p1_126m1_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p1_3p6_6m2_9m2_14p2_18p1_21m1_28m1_42p1_63p1_126m1_252p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 2, 2, 0, 3, 2, 0, 2, 2,
     8, 1, 2, -2, -2, -4, -4, -2, 0, -2, 1, 4, 0, 0, -12, -2, 1, 4, 4, -5,
     6, 4, 1, -4, -10, -2, -2, 0, -4, 0, -6, 0, -10, -2, -6, -8, -2, -1, 6, -4,
     -5, -10, 0, 1, 0, -2, 0, 8, 0, -6, 2, -4, 0, -8, 2, 2, 10, 0, -3, -16,
     -4, 2, -8, 0, -3, 12, 6, 2, -6, -4, 0, 2, 4, 2, 8, -2, 8, 12, 0, -6] := by
  eta_coeff

end WeightTwoCusps
