module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^(-2) η(2z)^4 η(8z)^(-1) η(11z)^2 η(16z) η(22z)^(-2) η(44z)^2 η(88z)^(-1) η(176z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(8z)^(-1) η(11z)^2 η(16z) η(22z)^(-2) η(44z)^2 η(88z)^(-1) η(176z)` at level 352. -/
abbrev cuspForm_352_eta_1m2_2p4_8m1_11p2_16p1_22m2_44p2_88m1_176p1 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 0 => -2, 1 => 4, 7 => -1, 10 => 2, 15 => 1, 21 => -2, 43 => 2, 87 => -1, 175 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_1m2_2p4_8m1_11p2_16p1_22m2_44p2_88m1_176p1_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_1m2_2p4_8m1_11p2_16p1_22m2_44p2_88m1_176p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 2, 0, 3, 2, 1, 4, 3, 2, -1,
     0, -1, 0, 5, -2, 1, 2, -4, 0, -2, 0, 5, 4, 0, -2, 3, 0, 2, 6, -1,
     2, 1, -6, -4, 0, 0, -4, -2, -4, -8, -2, -5, 0, 6, -4, -4, -4, -3, 0, 0,
     0, -2, 4, -2, -16, -1, 0, -4, 0, -10, -6, -5, -4, -7, -2, 4, 0, -1, -6, 0,
     4, -2, 2, 6, 0, -5, -4, -2, 2, 7, -4, -2, 0, -2, -4, -7, -4, 9, 8, -7] := by
  eta_coeff

end WeightTwoCusps
