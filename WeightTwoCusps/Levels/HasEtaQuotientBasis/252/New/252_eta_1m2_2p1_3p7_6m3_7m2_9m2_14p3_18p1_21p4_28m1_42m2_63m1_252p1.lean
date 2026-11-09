module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(7z)^(-2) η(9z)^(-2) η(14z)^3 η(18z) η(21z)^4 η(28z)^(-1) η(42z)^(-2) η(63z)^(-1) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(7z)^(-2) η(9z)^(-2) η(14z)^3 η(18z) η(21z)^4 η(28z)^(-1) η(42z)^(-2) η(63z)^(-1) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p3_18p1_21p4_28m1_42m2_63m1_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 6 => -2, 8 => -2, 13 => 3, 17 => 1, 20 => 4, 27 => -1, 41 => -2, 62 => -1, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p3_18p1_21p4_28m1_42m2_63m1_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p3_18p1_21p4_28m1_42m2_63m1_252p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 1, 0, -4, 1, 2, 4, 6, 0, 4,
     -10, 2, -2, 3, 4, -6, 8, -16, 2, -7, -2, -4, -14, 8, -12, 0, -6, -2, -10, -14,
     -4, 0, -2, 10, 11, 0, 0, -14, 4, 0, 22, 16, -8, 7, 0, 8, 0, 10, 10, -6,
     2, 16, -2, 2, 2, -2, -8, -4, 24, 4, 2, -1, 4, 0, 4, -4, 4, 3, 14, 6,
     12, 16, -16, 0, 2, 4, -18, -20, 8, -8, 4, -6, -15, -20, 12, 2, -8, -16, 0, 4] := by
  eta_coeff

end WeightTwoCusps
