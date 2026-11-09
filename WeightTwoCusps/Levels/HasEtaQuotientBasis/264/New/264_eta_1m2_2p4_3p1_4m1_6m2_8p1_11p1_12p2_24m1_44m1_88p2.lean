module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z) η(11z) η(12z)^2 η(24z)^(-1) η(44z)^(-1) η(88z)^2`; see
[the local level table](../../TABLE.md#level-264).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(6z)^(-2) η(8z) η(11z) η(12z)^2 η(24z)^(-1) η(44z)^(-1) η(88z)^2` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p4_3p1_4m1_6m2_8p1_11p1_12p2_24m1_44m1_88p2 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -2, 7 => 1, 10 => 1, 11 => 2, 23 => -1, 43 => -1, 87 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p4_3p1_4m1_6m2_8p1_11p1_12p2_24m1_44m1_88p2_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p4_3p1_4m1_6m2_8p1_11p1_12p2_24m1_44m1_88p2 =
    [0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 3, 3, 2, 0, 1, 2, 0, 1,
     0, 0, -1, -2, -1, -1, 2, 2, -3, -4, -1, 0, 2, -1, -2, -2, -3, 1, -2, -2,
     -2, -2, 0, -5, 0, -1, -4, 2, -4, -4, -2, 2, 3, -3, -2, 1, 1, 1, 0, -4,
     0, 3, 5, -3, -3, 4, 0, 0, 0, 0, 4, 0, 1, -4, -8, 2, 0, -1, -6, -2,
     -5, 2, 4, -4, -3, -2, 4, -3, 1, 3, 1, 2, -6, -5, -1, 2, 7, -5, -6, 0] := by
  eta_coeff

end WeightTwoCusps
