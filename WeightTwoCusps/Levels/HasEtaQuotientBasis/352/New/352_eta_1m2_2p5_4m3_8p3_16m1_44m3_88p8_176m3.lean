module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(16z)^(-1) η(44z)^(-3) η(88z)^8 η(176z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(16z)^(-1) η(44z)^(-3) η(88z)^8 η(176z)^(-3)` at level 352. -/
abbrev cuspForm_352_eta_1m2_2p5_4m3_8p3_16m1_44m3_88p8_176m3 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 43 => -3, 87 => 8, 175 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_1m2_2p5_4m3_8p3_16m1_44m3_88p8_176m3_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_1m2_2p5_4m3_8p3_16m1_44m3_88p8_176m3 =
    [0, 0, 1, 2, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, -2, 2, 0, 0, 2, -2,
     0, 0, 1, -2, 0, 0, -4, 2, 0, 0, -1, -2, 0, 0, -2, -2, 0, 0, 0, -2,
     0, 0, 2, 0, 0, 0, -1, 4, 0, 0, 8, 6, 0, 0, 1, 0, 0, 0, -8, 2,
     0, 0, 7, -4, 0, 0, 3, -6, 0, 0, -10, 6, 0, 0, -5, -8, 0, 0, -4, -8,
     0, 0, 0, -4, 0, 0, 2, 4, 0, 0, -10, -4, 0, 0, 0, 2, 0, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
