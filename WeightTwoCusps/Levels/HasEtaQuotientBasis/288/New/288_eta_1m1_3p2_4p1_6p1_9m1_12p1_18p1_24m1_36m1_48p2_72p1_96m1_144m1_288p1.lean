module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(6z) η(9z)^(-1) η(12z) η(18z) η(24z)^(-1) η(36z)^(-1) η(48z)^2 η(72z) η(96z)^(-1) η(144z)^(-1) η(288z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(6z) η(9z)^(-1) η(12z) η(18z) η(24z)^(-1) η(36z)^(-1) η(48z)^2 η(72z) η(96z)^(-1) η(144z)^(-1) η(288z)` at level 288. -/
abbrev cuspForm_288_eta_1m1_3p2_4p1_6p1_9m1_12p1_18p1_24m1_36m1_48p2_72p1_96m1_144m1_288p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 8 => -1, 11 => 1, 17 => 1, 23 => -1, 35 => -1, 47 => 2, 71 => 1, 95 => -1, 143 => -1, 287 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m1_3p2_4p1_6p1_9m1_12p1_18p1_24m1_36m1_48p2_72p1_96m1_144m1_288p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m1_3p2_4p1_6p1_9m1_12p1_18p1_24m1_36m1_48p2_72p1_96m1_144m1_288p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 2, 1, 2, 0, 3, 2, 4,
     1, 0, 0, 2, 0, -2, 1, 0, 4, -2, 0, -4, 0, 2, -2, -4, -2, 4, 1, 0,
     0, -1, 0, 0, -2, -2, 0, 4, 0, -4, -1, -4, -4, 2, 0, 0, -4, -2, -6, -3,
     -4, -4, -5, -2, 0, -8, -8, -4, -1, -4, 0, -10, 0, 2, -4, 0, -12, 0, 0, 0,
     0, -5, 6, 7, 0, -10, -5, -2, 0, 5, -4, -4, 4, 4, 0, -6, 0, 6, 4, 4] := by
  eta_coeff

end WeightTwoCusps
