module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(8z) η(16z) η(44z)^(-2) η(88z)^7 η(176z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(8z) η(16z) η(44z)^(-2) η(88z)^7 η(176z)^(-3)` at level 352. -/
abbrev cuspForm_352_eta_8p1_16p1_44m2_88p7_176m3 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 7 => 1, 15 => 1, 43 => -2, 87 => 7, 175 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_8p1_16p1_44m2_88p7_176m3_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_8p1_16p1_44m2_88p7_176m3 =
    [0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, -4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 4, 0, 0, 0, -4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
