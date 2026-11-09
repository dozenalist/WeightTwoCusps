module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 176

The eta expression is `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^(-2) η(22z)^4 η(44z) η(88z)^(-1)`; see
[the local level table](../../TABLE.md#level-176).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^(-2) η(22z)^4 η(44z) η(88z)^(-1)` at level 176. -/
abbrev cuspForm_176_eta_1m2_2p4_4p1_8m1_11m2_22p4_44p1_88m1 : gamma0CuspForms 176 :=
  etaQuotientCuspForm 176 sparse![176; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => -2, 21 => 4, 43 => 1, 87 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_1m2_2p4_4p1_8m1_11m2_22p4_44p1_88m1_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_1m2_2p4_4p1_8m1_11m2_22p4_44p1_88m1 =
    [0, 1, 2, 1, 2, 1, -2, 2, 0, -2, 2, -1, 2, 4, 0, 1, 0, -2, 4, 0,
     -6, 2, -2, 1, 0, -4, -4, -5, 4, 0, -2, -7, 0, -1, 0, 2, -4, 3, -4, 4,
     0, -8, -8, 6, -2, -2, 6, -8, 0, -3, 8, -2, -8, -6, 2, -1, 0, 0, -8, -5,
     -6, 12, -10, -4, 0, 4, 2, 7, 12, 1, 16, 3, 0, 4, -10, -4, 16, -2, 12, 10,
     0, 1, 4, 6, 4, -2, -4, 0, 0, 15, -12, 8, -6, -7, 8, 0, 0, -7, 10, 2] := by
  eta_coeff

end WeightTwoCusps
