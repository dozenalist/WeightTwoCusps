module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(6z)^(-1) η(8z)^2 η(9z)^(-1) η(16z)^(-1) η(144z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(6z)^(-1) η(8z)^2 η(9z)^(-1) η(16z)^(-1) η(144z)` at level 288. -/
abbrev cuspForm_288_eta_1m2_2p1_3p5_6m1_8p2_9m1_16m1_144p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 1, 2 => 5, 5 => -1, 7 => 2, 8 => -1, 15 => -1, 143 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m2_2p1_3p5_6m1_8p2_9m1_16m1_144p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m2_2p1_3p5_6m1_8p2_9m1_16m1_144p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 4, 3, 4, 4, 6, 6, 2, 4, 0, 6, 1, 2,
     0, 0, 8, 0, 0, -6, 2, 4, 0, 0, -2, -2, 0, 0, -4, -8, -6, 0, -6, -8,
     0, -6, 0, -2, 0, -6, -16, 8, 0, 0, -2, -8, 0, -12, 1, -4, -16, 0, -12, -4,
     -12, 0, 6, -4, 0, 0, -4, -2, 0, 0, 0, -16, 0, -6, -8, 0, 0, 12, -2, -2,
     0, -9, 12, 12, 0, -18, -2, 12, 0, -6, -2, -4, 0, 0, 0, -8, 0, 18, 8, 4] := by
  eta_coeff

end WeightTwoCusps
