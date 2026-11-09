module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^7 η(4z)^(-3) η(7z) η(9z) η(12z) η(18z)^(-1) η(21z)^2 η(42z)^(-1) η(63z)^(-1) η(126z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(4z)^(-3) η(7z) η(9z) η(12z) η(18z)^(-1) η(21z)^2 η(42z)^(-1) η(63z)^(-1) η(126z)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p7_4m3_7p1_9p1_12p1_18m1_21p2_42m1_63m1_126p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 7, 3 => -3, 6 => 1, 8 => 1, 11 => 1, 17 => -1, 20 => 2, 41 => -1, 62 => -1, 125 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p7_4m3_7p1_9p1_12p1_18m1_21p2_42m1_63m1_126p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p7_4m3_7p1_9p1_12p1_18m1_21p2_42m1_63m1_126p1 =
    [0, 0, 0, 1, 3, 2, 1, 5, 5, 3, 4, 3, 7, 6, 1, 6, 4, 2, 3, 2,
     8, 1, -1, 11, 3, -4, -2, 1, 2, -7, -4, -4, -6, -10, -16, -2, -9, -14, 0, 0,
     -6, -16, -3, 6, -15, -4, -1, -6, -1, -24, -8, -8, -12, 3, -11, 6, -4, -14, 13, -8,
     -12, 12, -2, 5, -5, -20, -20, -8, 8, -14, 2, 5, 5, 6, -6, 7, 8, 9, 28, 4,
     -6, -3, -18, 14, -5, -4, 12, 18, 7, -8, 10, 4, 5, 20, 18, 0, 7, -6, 0, -18] := by
  eta_coeff

end WeightTwoCusps
