module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 176

The eta expression is `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(22z) η(44z)^(-2) η(88z)^5 η(176z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(22z) η(44z)^(-2) η(88z)^5 η(176z)^(-2)` at level 176. -/
abbrev cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2 : gamma0CuspForms 176 :=
  etaQuotientCuspForm 176 sparse![176; 0 => -2, 1 => 6, 3 => -2, 21 => 1, 43 => -2, 87 => 5, 175 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2 =
    [0, 1, 2, -1, -2, 1, -2, -2, 0, -2, 2, 1, 0, 0, -2, 3, 2, 2, 0, 0,
     2, -2, 0, -1, 0, 0, 2, 1, 0, 0, -2, 3, -4, -1, -2, -2, 4, -1, -2, -4,
     0, -4, -2, 2, 0, 2, 2, 0, -2, 1, 0, 2, 0, -2, 6, 1, 0, 4, -4, 1,
     4, 4, 2, 4, 4, 0, 0, -7, -4, 1, 6, -3, 0, 0, -2, 4, -8, -2, 2, -2,
     2, -3, -6, -6, -4, -6, -8, 0, 0, 3, -8, 4, 4, -3, 12, 8, 4, 1, 2, -2] := by
  eta_coeff

end WeightTwoCusps
