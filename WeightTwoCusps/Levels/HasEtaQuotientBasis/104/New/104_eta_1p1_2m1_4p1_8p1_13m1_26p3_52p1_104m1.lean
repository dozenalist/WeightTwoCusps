module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 104

The eta expression is `η(z) η(2z)^(-1) η(4z) η(8z) η(13z)^(-1) η(26z)^3 η(52z) η(104z)^(-1)`; see
[the local level table](../../TABLE.md#level-104).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(4z) η(8z) η(13z)^(-1) η(26z)^3 η(52z) η(104z)^(-1)` at level 104. -/
abbrev cuspForm_104_eta_1p1_2m1_4p1_8p1_13m1_26p3_52p1_104m1 : gamma0CuspForms 104 :=
  etaQuotientCuspForm 104 sparse![104; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 12 => -1, 25 => 3, 51 => 1, 103 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1p1_2m1_4p1_8p1_13m1_26p3_52p1_104m1_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1p1_2m1_4p1_8p1_13m1_26p3_52p1_104m1 =
    [0, 1, -1, 0, -1, 0, 0, 1, 0, -1, 1, 1, 1, 0, 1, -2, -1, -2, 1, -1,
     2, 0, -2, 0, 2, 1, 0, -2, 0, 0, 1, 1, 0, 0, 0, 0, -2, 0, 0, 0,
     -1, 2, 1, 2, -2, 0, -2, 1, 1, 1, -1, 2, 0, -2, 4, -2, -1, 0, -4, -3,
     0, 2, -2, -1, -1, 0, -4, 7, 3, 4, 0, 3, -4, -2, 5, -2, -4, -2, -1, 6,
     2, 1, 2, -5, 2, 0, 0, 0, 4, -2, 0, -1, 2, -4, -3, -6, 2, -2, 5, -3] := by
  eta_coeff

end WeightTwoCusps
