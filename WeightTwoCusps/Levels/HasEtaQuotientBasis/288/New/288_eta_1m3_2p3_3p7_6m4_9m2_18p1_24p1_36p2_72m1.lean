module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-4) η(9z)^(-2) η(18z) η(24z) η(36z)^2 η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-4) η(9z)^(-2) η(18z) η(24z) η(36z)^2 η(72z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m3_2p3_3p7_6m4_9m2_18p1_24p1_36p2_72m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 3, 2 => 7, 5 => -4, 8 => -2, 17 => 1, 23 => 1, 35 => 2, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m3_2p3_3p7_6m4_9m2_18p1_24p1_36p2_72m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m3_2p3_3p7_6m4_9m2_18p1_24p1_36p2_72m1 =
    [0, 1, 3, 6, 6, 3, 0, 0, 6, 6, 6, 0, 0, 6, 6, 12, 0, 3, 0, 0,
     6, 0, 12, 0, 0, -1, 0, 6, 0, 3, 0, 0, 0, 0, -6, 0, 0, -2, -6, -12,
     0, -9, 0, 0, -12, -12, -24, 0, 0, -7, -9, -36, -12, -9, 0, 0, -24, 0, -18, 0,
     0, -10, -6, -24, 0, -6, 0, 0, -6, 0, 0, 0, 0, -6, -6, -6, -24, 0, 0, 0,
     0, -18, 18, 0, 0, -4, -18, 12, 0, 3, 0, 0, 24, 0, 0, 0, 0, 18, 3, 24] := by
  eta_coeff

end WeightTwoCusps
