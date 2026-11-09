module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-2) η(12z) η(14z)^5 η(28z)^(-2) η(63z) η(126z)^(-1) η(252z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-2) η(12z) η(14z)^5 η(28z)^(-2) η(63z) η(126z)^(-1) η(252z)` at level 252. -/
abbrev cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m2_12p1_14p5_28m2_63p1_126m1_252p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -2, 11 => 1, 13 => 5, 27 => -2, 62 => 1, 125 => -1, 251 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m2_12p1_14p5_28m2_63p1_126m1_252p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m2_12p1_14p5_28m2_63p1_126m1_252p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, -1, 0, 4, 1, 2, 8, 10, 2, -4,
     6, 2, -4, 1, 4, 12, -8, -12, 0, -9, 2, 0, 6, 0, -16, 0, -4, 4, 6, -6,
     -4, 8, 2, -12, -5, 0, 8, -18, -4, 0, -14, 8, -4, 9, -12, -16, 0, 2, 4, -10,
     -2, -20, -2, 4, -4, -2, -8, 0, -16, -4, 8, 1, 6, 8, 0, -4, 4, 1, 2, -4,
     -4, 10, -24, -8, -2, -8, 18, -4, 0, -8, 4, 8, 5, -4, 0, 2, 0, 32, 0, -4] := by
  eta_coeff

end WeightTwoCusps
