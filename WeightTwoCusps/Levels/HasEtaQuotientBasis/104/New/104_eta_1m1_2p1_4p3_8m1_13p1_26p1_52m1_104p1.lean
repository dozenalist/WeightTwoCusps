module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 104

The eta expression is `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-1) η(13z) η(26z) η(52z)^(-1) η(104z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-1) η(13z) η(26z) η(52z)^(-1) η(104z)` at level 104. -/
abbrev cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1 : gamma0CuspForms 104 :=
  etaQuotientCuspForm 104 sparse![104; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 12 => 1, 25 => 1, 51 => -1, 103 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1 =
    [0, 0, 0, 0, 1, 1, 1, 2, -1, 0, 1, -1, 1, 0, -1, -1, 1, -2, -3, -1,
     -3, 1, 0, -2, -1, 0, 0, 2, -1, -4, -1, -1, -1, -4, 3, 0, -2, 5, -4, -1,
     3, 4, 1, 2, 6, 0, 4, -2, 1, 6, 1, 2, 1, -6, 3, 8, 1, 2, 0, 5,
     -3, 0, 2, -5, 1, 2, -2, -3, -3, 2, -1, 2, 2, -2, -3, -6, 2, 0, -1, 4,
     -3, -4, -2, -9, -1, -9, 3, -2, -6, 2, 0, -1, 0, 0, -5, 2, -1, 0, 1, 3] := by
  eta_coeff

end WeightTwoCusps
