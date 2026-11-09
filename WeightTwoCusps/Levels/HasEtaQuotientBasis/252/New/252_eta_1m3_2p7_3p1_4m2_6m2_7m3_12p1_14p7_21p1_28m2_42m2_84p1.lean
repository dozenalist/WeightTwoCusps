module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(7z)^(-3) η(12z) η(14z)^7 η(21z) η(28z)^(-2) η(42z)^(-2) η(84z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(7z)^(-3) η(12z) η(14z)^7 η(21z) η(28z)^(-2) η(42z)^(-2) η(84z)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p7_3p1_4m2_6m2_7m3_12p1_14p7_21p1_28m2_42m2_84p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 6 => -3, 11 => 1, 13 => 7, 20 => 1, 27 => -2, 41 => -2, 83 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p7_3p1_4m2_6m2_7m3_12p1_14p7_21p1_28m2_42m2_84p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p7_3p1_4m2_6m2_7m3_12p1_14p7_21p1_28m2_42m2_84p1 =
    [0, 0, 1, 3, 2, 0, 1, 0, 1, 6, 9, 6, -1, 3, 1, 0, 11, 6, 4, -3,
     0, 3, -9, 6, 1, 0, -4, -9, 2, -12, 0, 6, 1, -12, -12, 0, -4, 0, 2, 0,
     -27, -6, 1, -6, 0, 0, 9, -24, -1, 0, -5, 6, 1, 12, -11, 0, 1, -6, 3, -6,
     0, -9, -4, 6, -16, 0, 0, 6, -6, -12, 9, -6, 4, -6, 2, -15, -5, 6, -4, -6,
     0, 12, -30, 6, -1, 0, 8, 6, 27, -18, 0, 3, 0, 12, -12, 0, 1, 0, 1, -12] := by
  eta_coeff

end WeightTwoCusps
