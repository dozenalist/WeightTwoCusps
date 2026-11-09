module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(7z)^2 η(11z)^2 η(14z)^(-1) η(22z)^(-2) η(44z) η(77z)^(-2) η(154z)^5 η(308z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(7z)^2 η(11z)^2 η(14z)^(-1) η(22z)^(-2) η(44z) η(77z)^(-2) η(154z)^5 η(308z)^(-2)` at level 308. -/
abbrev cuspForm_308_eta_1m2_2p4_4m1_7p2_11p2_14m1_22m2_44p1_77m2_154p5_308m2 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => -2, 1 => 4, 3 => -1, 6 => 2, 10 => 2, 13 => -1, 21 => -2, 43 => 1, 76 => -2, 153 => 5, 307 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1m2_2p4_4m1_7p2_11p2_14m1_22m2_44p1_77m2_154p5_308m2_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1m2_2p4_4m1_7p2_11p2_14m1_22m2_44p1_77m2_154p5_308m2 =
    [0, 1, 2, 1, 2, 3, 2, 4, 2, 0, 4, 3, 0, 0, 0, -1, 0, 0, -6, 0,
     6, -4, 0, 1, -4, 4, 0, -5, 0, 6, 0, -5, 4, -3, -2, 4, -8, -1, 2, -6,
     -6, -4, 0, -10, -4, 0, -6, 6, -4, -7, 4, 2, 0, -10, 2, 3, -2, 4, -12, 3,
     6, -6, -8, -8, 6, -2, -6, 1, -6, 5, 0, -7, 4, 4, 10, -8, 6, 6, -6, 12,
     -6, 3, 18, 2, 0, 4, 14, 2, 0, 3, -10, 16, -4, -15, 6, 2, 4, 9, 2, 2] := by
  eta_coeff

end WeightTwoCusps
