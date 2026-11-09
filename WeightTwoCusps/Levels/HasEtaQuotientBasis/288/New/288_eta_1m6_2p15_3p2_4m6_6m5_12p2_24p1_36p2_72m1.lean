module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-5) η(12z)^2 η(24z) η(36z)^2 η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-5) η(12z)^2 η(24z) η(36z)^2 η(72z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m6_2p15_3p2_4m6_6m5_12p2_24p1_36p2_72m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -5, 11 => 2, 23 => 1, 35 => 2, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m6_2p15_3p2_4m6_6m5_12p2_24p1_36p2_72m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m6_2p15_3p2_4m6_6m5_12p2_24p1_36p2_72m1 =
    [0, 1, 6, 12, 6, -6, 0, 12, 12, 12, 6, 0, 0, -6, 12, 24, 0, -6, 0, 12,
     12, 0, 12, 0, 0, 11, 0, 12, 0, -6, 0, -12, 0, 0, -6, 0, 0, -2, -12, -24,
     0, 18, 0, -12, -24, -24, -24, 0, 0, -7, -18, -72, -12, 18, 0, -24, -48, 0, -18, 0,
     0, -10, -12, -48, 0, 12, 0, -12, -12, 0, 0, 0, 0, 6, -12, -12, -24, 0, 0, -12,
     0, -36, 18, 0, 0, 32, -36, 24, 0, -6, 0, -24, 48, 0, 0, 0, 0, -18, 6, 48] := by
  eta_coeff

end WeightTwoCusps
