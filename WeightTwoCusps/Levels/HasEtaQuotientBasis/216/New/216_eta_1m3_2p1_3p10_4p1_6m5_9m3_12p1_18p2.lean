module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-3) η(2z) η(3z)^10 η(4z) η(6z)^(-5) η(9z)^(-3) η(12z) η(18z)^2`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z) η(3z)^10 η(4z) η(6z)^(-5) η(9z)^(-3) η(12z) η(18z)^2` at level 216. -/
abbrev cuspForm_216_eta_1m3_2p1_3p10_4p1_6m5_9m3_12p1_18p2 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -3, 1 => 1, 2 => 10, 3 => 1, 5 => -5, 8 => -3, 11 => 1, 17 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p1_3p10_4p1_6m5_9m3_12p1_18p2_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p1_3p10_4p1_6m5_9m3_12p1_18p2 =
    [0, 1, 3, 8, 9, 10, 0, 3, 0, 16, 9, 10, 0, 4, 15, 8, 9, -10, 0, 2,
     0, 0, -9, 10, 0, -4, -21, -16, -9, 0, 0, -7, 0, -16, 0, -30, 0, -6, -3, -16,
     -27, 0, 0, -2, 0, -32, -18, -30, 0, 2, -15, -8, -36, -20, 0, -5, 0, -32, 18, 10,
     0, -8, -12, 0, 9, 10, 0, -10, 0, 32, -9, 20, 0, 1, -3, -8, 18, -30, 0, 16,
     0, 16, -18, 20, 0, 8, 24, -24, 27, 30, 0, 12, 0, 64, 18, -10, 0, -1, 54, 64] := by
  eta_coeff

end WeightTwoCusps
