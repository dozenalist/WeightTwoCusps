module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^8 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z) η(13z) η(26z)^(-1) η(78z)^2`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z) η(13z) η(26z)^(-1) η(78z)^2` at level 468. -/
abbrev cuspForm_468_eta_1m3_2p8_3p2_4m3_6m3_12p1_13p1_26m1_78p2 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 8, 2 => 2, 3 => -3, 5 => -3, 11 => 1, 12 => 1, 25 => -1, 77 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m3_2p8_3p2_4m3_6m3_12p1_13p1_26m1_78p2_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m3_2p8_3p2_4m3_6m3_12p1_13p1_26m1_78p2 =
    [0, 0, 0, 0, 0, 0, 1, 3, 1, -4, -4, -1, 2, 1, -2, 0, -4, -2, 5, 1,
     1, -2, 4, 8, -1, 2, -1, 0, 1, 4, 4, -7, -3, -4, -1, -6, -4, 4, -6, 0,
     2, 2, -2, -2, 2, -2, -2, -1, 6, 0, -1, 0, -1, 6, 1, 6, 4, -2, 5, -2,
     2, 2, -2, 2, -2, 1, -4, -7, -8, 0, 2, -2, 3, -2, 8, 8, 1, 4, -1, -4,
     4, 8, -2, -6, -6, -10, -2, 4, 2, 2, -12, -1, 4, -10, 8, 0, -9, -2, 1, 10] := by
  eta_coeff

end WeightTwoCusps
