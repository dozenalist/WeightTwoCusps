module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-4) η(2z)^9 η(3z) η(4z)^(-2) η(6z)^(-3) η(9z) η(12z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^9 η(3z) η(4z)^(-2) η(6z)^(-3) η(9z) η(12z)^2` at level 216. -/
abbrev cuspForm_216_eta_1m4_2p9_3p1_4m2_6m3_9p1_12p2 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -4, 1 => 9, 2 => 1, 3 => -2, 5 => -3, 8 => 1, 11 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m4_2p9_3p1_4m2_6m3_9p1_12p2_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m4_2p9_3p1_4m2_6m3_9p1_12p2 =
    [0, 1, 4, 5, 3, 4, 3, 3, 12, 10, 3, 4, 0, 4, 8, 5, 3, -4, 0, 2,
     0, 0, -3, 4, 0, -4, -4, -10, -3, 0, 0, -7, -24, -10, 0, -12, 0, -6, -16, -10,
     -9, 0, -12, -2, 0, -20, -6, -12, 0, 2, -20, -5, -12, -8, 0, -5, -12, -20, 6, 4,
     0, -8, -16, 0, 3, 4, 0, -10, 0, 20, -3, 8, 0, 1, 20, -5, 6, -12, 6, 16,
     0, 10, -6, 8, 0, 8, 32, -15, 9, 12, 0, 12, 0, 40, 6, -4, 0, -1, 24, 40] := by
  eta_coeff

end WeightTwoCusps
