module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(7z) η(11z) η(14z)^(-2) η(22z)^(-2) η(28z) η(44z) η(77z)^(-3) η(154z)^8 η(308z)^(-3)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(7z) η(11z) η(14z)^(-2) η(22z)^(-2) η(28z) η(44z) η(77z)^(-3) η(154z)^8 η(308z)^(-3)` at level 308. -/
abbrev cuspForm_308_eta_1m3_2p8_4m3_7p1_11p1_14m2_22m2_28p1_44p1_77m3_154p8_308m3 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => -3, 1 => 8, 3 => -3, 6 => 1, 10 => 1, 13 => -2, 21 => -2, 27 => 1, 43 => 1, 76 => -3, 153 => 8, 307 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1m3_2p8_4m3_7p1_11p1_14m2_22m2_28p1_44p1_77m3_154p8_308m3_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1m3_2p8_4m3_7p1_11p1_14m2_22m2_28p1_44p1_77m3_154p8_308m3 =
    [0, 0, 0, 0, 1, 3, 1, -2, 2, 1, -4, -2, -5, -1, 4, -7, -5, 1, 2, 4,
     0, 2, 6, 9, -1, -9, -1, 3, 5, -6, -4, 6, 2, 4, -7, -3, 15, 1, -10, -6,
     -2, -1, -3, -2, -5, 16, 12, -7, 9, 2, 12, 4, -13, -4, -12, -1, -14, -20, 4, 6,
     0, -3, 5, 1, 7, 14, -11, 9, 7, -19, 8, -5, -2, 13, 6, 11, -8, -4, -6, -6,
     2, -12, -3, -14, -1, -2, -16, 22, 8, 17, 22, -13, 0, 9, -3, -10, -1, 5, -4, -5] := by
  eta_coeff

end WeightTwoCusps
