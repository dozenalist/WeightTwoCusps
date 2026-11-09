module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^(-1) η(2z) η(4z) η(7z)^2 η(11z) η(14z)^(-1) η(22z) η(44z)^(-1) η(154z)^(-1) η(308z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z) η(7z)^2 η(11z) η(14z)^(-1) η(22z) η(44z)^(-1) η(154z)^(-1) η(308z)^2` at level 308. -/
abbrev cuspForm_308_eta_1m1_2p1_4p1_7p2_11p1_14m1_22p1_44m1_154m1_308p2 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => -1, 1 => 1, 3 => 1, 6 => 2, 10 => 1, 13 => -1, 21 => 1, 43 => -1, 153 => -1, 307 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1m1_2p1_4p1_7p2_11p1_14m1_22p1_44m1_154m1_308p2_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1m1_2p1_4p1_7p2_11p1_14m1_22p1_44m1_154m1_308p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 2, 0, 0, 3, 1, -1, 3, 0, 2,
     4, -3, -2, 1, -3, -2, -4, -5, -1, 2, -2, -4, 0, -3, 0, 1, -7, -1, 3, -6,
     0, -5, -6, 0, 1, -4, -2, 3, 0, 0, 0, -8, -6, 3, -6, 1, 0, -1, 2, 2,
     -2, -2, 1, 1, 0, 2, -5, -3, 1, -6, -2, -4, -5, 3, 8, -1, -2, -4, -4, -1] := by
  eta_coeff

end WeightTwoCusps
