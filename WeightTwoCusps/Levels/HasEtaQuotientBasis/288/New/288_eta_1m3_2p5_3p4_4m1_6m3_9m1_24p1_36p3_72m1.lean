module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-1) η(6z)^(-3) η(9z)^(-1) η(24z) η(36z)^3 η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-1) η(6z)^(-3) η(9z)^(-1) η(24z) η(36z)^3 η(72z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m3_2p5_3p4_4m1_6m3_9m1_24p1_36p3_72m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 5, 2 => 4, 3 => -1, 5 => -3, 8 => -1, 23 => 1, 35 => 3, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m3_2p5_3p4_4m1_6m3_9m1_24p1_36p3_72m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m3_2p5_3p4_4m1_6m3_9m1_24p1_36p3_72m1 =
    [0, 0, 1, 3, 4, 3, 0, 0, 2, 3, 4, 0, 0, 0, 2, 6, 0, 3, 0, 0,
     2, 0, 8, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, -4, 0, 0, 0, -2, -6,
     0, -9, 0, 0, -4, -6, -16, 0, 0, 0, -3, -18, -8, -9, 0, 0, -8, 0, -12, 0,
     0, 0, -2, -12, 0, -6, 0, 0, -2, 0, 0, 0, 0, 0, -2, -3, -16, 0, 0, 0,
     0, -9, 12, 0, 0, 0, -6, 6, 0, 3, 0, 0, 8, 0, 0, 0, 0, 0, 1, 12] := by
  eta_coeff

end WeightTwoCusps
