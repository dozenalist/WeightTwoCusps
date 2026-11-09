module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-4) η(12z) η(14z)^10 η(21z) η(28z)^(-4) η(42z)^(-2) η(84z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-4) η(12z) η(14z)^10 η(21z) η(28z)^(-4) η(42z)^(-2) η(84z)` at level 252. -/
abbrev cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m4_12p1_14p10_21p1_28m4_42m2_84p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -4, 11 => 1, 13 => 10, 20 => 1, 27 => -4, 41 => -2, 83 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m4_12p1_14p10_21p1_28m4_42m2_84p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m4_12p1_14p10_21p1_28m4_42m2_84p1 =
    [0, 1, 4, 4, -1, 0, 4, 1, 4, 16, 18, 0, -4, 14, 4, 0, 17, 24, 16, -16,
     0, 4, -18, 0, 4, 31, -16, -44, -1, -24, 0, -4, 4, 0, -30, 0, -16, 2, 8, -16,
     -18, 24, 4, -28, 0, 0, 18, -48, -4, 1, -20, 24, -14, 24, -44, -36, 4, 8, 12, -24,
     0, -46, -16, 16, -1, 0, 0, -4, -24, 0, 18, 0, 16, 38, 8, -20, 16, 0, -16, 8,
     0, 40, -66, -24, -4, -36, 32, -24, 18, -24, 0, 14, 0, -16, -12, 0, 4, 62, 4, 0] := by
  eta_coeff

end WeightTwoCusps
