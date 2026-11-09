module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(11z) η(22z)^(-1) η(88z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(11z) η(22z)^(-1) η(88z)^2` at level 352. -/
abbrev cuspForm_352_eta_1m3_2p7_4m2_11p1_22m1_88p2 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 0 => -3, 1 => 7, 3 => -2, 10 => 1, 21 => -1, 87 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_1m3_2p7_4m2_11p1_22m1_88p2_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_1m3_2p7_4m2_11p1_22m1_88p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 1, 4, 2, 1, 4, 0, 2, 5, 1, -1,
     -2, 1, -1, 2, 1, -4, 6, -2, -4, 2, -2, 2, 2, 1, -4, 1, 2, -4, 4, 1,
     -5, -3, -2, -2, 0, -2, -2, -2, -2, -4, -7, 1, 4, 6, -4, -7, 2, -1, 2, -2,
     2, 6, -2, -2, -8, -3, -1, -2, 0, -8, 0, 0, -6, 1, 3, 0, 0, 1, 0, -2,
     2, -2, -2, 4, -4, -7, -4, 2, -1, 2, -4, -2, 2, -8, -4, -1, -2, 0, 4, -11] := by
  eta_coeff

end WeightTwoCusps
