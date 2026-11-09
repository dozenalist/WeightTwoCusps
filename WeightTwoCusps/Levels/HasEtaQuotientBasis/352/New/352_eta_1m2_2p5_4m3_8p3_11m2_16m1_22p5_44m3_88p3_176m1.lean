module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(11z)^(-2) η(16z)^(-1) η(22z)^5 η(44z)^(-3) η(88z)^3 η(176z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(11z)^(-2) η(16z)^(-1) η(22z)^5 η(44z)^(-3) η(88z)^3 η(176z)^(-1)` at level 352. -/
abbrev cuspForm_352_eta_1m2_2p5_4m3_8p3_11m2_16m1_22p5_44m3_88p3_176m1 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 10 => -2, 15 => -1, 21 => 5, 43 => -3, 87 => 3, 175 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_1m2_2p5_4m3_8p3_11m2_16m1_22p5_44m3_88p3_176m1_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_1m2_2p5_4m3_8p3_11m2_16m1_22p5_44m3_88p3_176m1 =
    [0, 0, 1, 2, 0, 0, 3, 2, 0, 0, 1, 0, 0, 2, 2, 2, 0, 6, 6, -2,
     0, 2, 1, -2, 0, -4, 0, 2, 0, 4, -5, -2, 0, 2, -6, -2, 0, -8, 4, -2,
     0, -2, -2, 0, 0, -4, -5, 4, 0, 0, 4, 6, 0, 4, 1, 0, 0, -6, -8, 2,
     0, 4, 11, -4, 0, -2, 3, -6, 0, -8, -14, 6, 0, 6, -5, -8, 0, 2, -8, -8,
     0, -4, 4, -4, 0, -6, -6, 4, 0, 0, -18, -4, 0, 0, 0, 2, 0, -4, 5, 0] := by
  eta_coeff

end WeightTwoCusps
