module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 104

The eta expression is `η(z) η(8z) η(13z)^(-1) η(26z)^2 η(52z)^2 η(104z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z) η(8z) η(13z)^(-1) η(26z)^2 η(52z)^2 η(104z)^(-1)` at level 104. -/
abbrev cuspForm_104_eta_1p1_8p1_13m1_26p2_52p2_104m1 : gamma0CuspForms 104 :=
  etaQuotientCuspForm 104 sparse![104; 0 => 1, 7 => 1, 12 => -1, 25 => 2, 51 => 2, 103 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1p1_8p1_13m1_26p2_52p2_104m1_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1p1_8p1_13m1_26p2_52p2_104m1 =
    [0, 0, 1, -1, -1, 0, 0, 1, 0, 1, -1, 1, 1, 0, -1, 0, -1, -3, -1, 1,
     2, 0, 2, -2, 2, 1, 0, -1, 0, 0, -1, -1, 0, 2, 0, 1, -2, 0, 0, 0,
     -1, 2, -1, -1, -2, 0, 2, 1, 1, -1, 1, 1, 0, 0, -4, 2, -1, -4, 4, -1,
     0, -2, 2, 1, -1, 1, 4, -1, 3, 6, 0, -1, -4, -2, -5, 2, -4, -2, 1, 0,
     2, 0, -2, -1, 2, -4, 0, 0, 4, 2, 0, 0, 2, -4, 3, 0, 2, 4, -5, -1] := by
  eta_coeff

end WeightTwoCusps
