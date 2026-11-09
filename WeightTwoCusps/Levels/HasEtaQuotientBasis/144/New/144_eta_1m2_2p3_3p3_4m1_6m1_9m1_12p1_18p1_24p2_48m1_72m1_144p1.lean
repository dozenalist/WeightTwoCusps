module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-1) η(9z)^(-1) η(12z) η(18z) η(24z)^2 η(48z)^(-1) η(72z)^(-1) η(144z)`; see
[the local level table](../../TABLE.md#level-144).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-1) η(9z)^(-1) η(12z) η(18z) η(24z)^2 η(48z)^(-1) η(72z)^(-1) η(144z)` at level 144. -/
abbrev cuspForm_144_eta_1m2_2p3_3p3_4m1_6m1_9m1_12p1_18p1_24p2_48m1_72m1_144p1 : gamma0CuspForms 144 :=
  etaQuotientCuspForm 144 sparse![144; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 8 => -1, 11 => 1, 17 => 1, 23 => 2, 47 => -1, 71 => -1, 143 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m2_2p3_3p3_4m1_6m1_9m1_12p1_18p1_24p2_48m1_72m1_144p1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m2_2p3_3p3_4m1_6m1_9m1_12p1_18p1_24p2_48m1_72m1_144p1 =
    [0, 0, 0, 0, 1, 2, 2, 1, 0, 2, 1, 0, 0, 1, 4, 0, 0, -2, -2, 1,
     0, 0, -2, 0, 0, -1, -4, 0, -4, -6, -4, -5, 0, -8, -1, 0, 0, -4, -12, 0,
     0, 6, 0, -5, 0, -4, 4, 0, 0, 4, 4, 0, 2, 2, 2, 6, 0, 8, -3, 0,
     0, 4, 12, 0, 0, -4, 8, 7, 0, 16, 0, 0, 0, -5, 16, 0, 8, 0, -4, 7,
     0, 2, 3, 0, 0, 1, -4, 0, 0, 6, 4, 2, 0, -16, 0, 0, 0, 3, -16, 0] := by
  eta_coeff

end WeightTwoCusps
