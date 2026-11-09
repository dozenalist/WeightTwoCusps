module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-1) η(12z) η(21z)^3 η(28z) η(63z)^(-1) η(84z)^(-1) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-1) η(12z) η(21z)^3 η(28z) η(63z)^(-1) η(84z)^(-1) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m1_12p1_21p3_28p1_63m1_84m1_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -1, 11 => 1, 20 => 3, 27 => 1, 62 => -1, 83 => -1, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m1_12p1_21p3_28p1_63m1_84m1_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m1_12p1_21p3_28p1_63m1_84m1_252p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, -1, 0, 4, 1, 1, 4, 6, 3, -4,
     2, 1, -2, 9, 10, 6, -4, -2, 2, -5, 1, 4, 10, -8, -12, 0, -12, 2, 2, 5,
     -4, -12, 1, -10, -1, 0, 0, -10, -2, 0, -14, -4, -8, 5, -18, -8, 0, -7, 10, -6,
     -1, -16, -2, 4, 2, -10, -20, 4, -24, -10, 2, 1, 13, 0, -8, -2, 4, 9, 17, -6,
     0, -1, -16, 12, -1, -4, 18, 14, 8, -4, 10, 6, 9, 14, 12, 10, -8, 16, 0, -10] := by
  eta_coeff

end WeightTwoCusps
