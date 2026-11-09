module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^3 η(4z)^(-3) η(6z)^(-3) η(7z)^2 η(12z) η(14z)^(-1) η(21z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^3 η(4z)^(-3) η(6z)^(-3) η(7z)^2 η(12z) η(14z)^(-1) η(21z)` at level 252. -/
abbrev cuspForm_252_eta_1m4_2p8_3p3_4m3_6m3_7p2_12p1_14m1_21p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -4, 1 => 8, 2 => 3, 3 => -3, 5 => -3, 6 => 2, 11 => 1, 13 => -1, 20 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m4_2p8_3p3_4m3_6m3_7p2_12p1_14m1_21p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m4_2p8_3p3_4m3_6m3_7p2_12p1_14m1_21p1 =
    [0, 1, 4, 6, 5, 4, 6, 11, 10, 4, 4, 6, 10, 8, 2, 6, 3, 4, 10, 6,
     8, 0, 0, 10, -6, -7, -4, -6, 1, -14, -6, 0, -12, -8, -14, -4, -4, -8, 0, -10,
     -8, -8, 0, 2, -26, -8, -2, -12, -10, -47, -16, -4, -12, 6, -30, -12, -4, -14, 10, -16,
     -26, -4, -12, 8, -13, -28, -8, -8, 16, -4, 2, 10, -2, -10, -8, 6, 10, 6, 2, -14,
     -12, 10, -14, 4, -16, 4, 20, 0, 6, -16, 4, 22, 10, 12, 12, -12, 38, 26, 4, -12] := by
  eta_coeff

end WeightTwoCusps
