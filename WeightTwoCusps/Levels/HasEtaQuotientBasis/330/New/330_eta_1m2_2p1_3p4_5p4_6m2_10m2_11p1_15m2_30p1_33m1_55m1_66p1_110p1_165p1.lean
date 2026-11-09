module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-2) η(10z)^(-2) η(11z) η(15z)^(-2) η(30z) η(33z)^(-1) η(55z)^(-1) η(66z) η(110z) η(165z)`; see
[the local level table](../../TABLE.md#level-330).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-2) η(10z)^(-2) η(11z) η(15z)^(-2) η(30z) η(33z)^(-1) η(55z)^(-1) η(66z) η(110z) η(165z)` at level 330. -/
abbrev cuspForm_330_eta_1m2_2p1_3p4_5p4_6m2_10m2_11p1_15m2_30p1_33m1_55m1_66p1_110p1_165p1 : gamma0CuspForms 330 :=
  etaQuotientCuspForm 330 sparse![330; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 29 => 1, 32 => -1, 54 => -1, 65 => 1, 109 => 1, 164 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_330_eta_1m2_2p1_3p4_5p4_6m2_10m2_11p1_15m2_30p1_33m1_55m1_66p1_110p1_165p1_first_coeffs :
    first_coeffs 100 cuspForm_330_eta_1m2_2p1_3p4_5p4_6m2_10m2_11p1_15m2_30p1_33m1_55m1_66p1_110p1_165p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 4, 6, 4, 4, 0, 4,
     2, 4, -1, 2, -4, -4, -4, 6, 4, 4, 0, 2, -4, -1, 2, 4, -2, -8, -10, -12,
     -4, -4, -2, 0, 1, -2, -4, 8, 4, -2, -4, 4, -4, -6, 0, -1, -10, -4, -4, 0,
     -4, 8, 0, -4, 6, -4, 1, -6, 12, -8, 0, -6, -4, -8, 4, 8, 4, 0, 0, -16,
     0, -2, 6, 4, 0, 0, -18, 4, -1, 2, 0, 0, 0, -12, 0, -12, 4, -8, -8, 1] := by
  eta_coeff

end WeightTwoCusps
