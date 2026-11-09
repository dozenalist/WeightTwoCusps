module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-4) η(12z) η(24z) η(36z)^2 η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-4) η(12z) η(24z) η(36z)^2 η(72z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m4_2p8_3p4_4m3_6m4_12p1_24p1_36p2_72m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -4, 11 => 1, 23 => 1, 35 => 2, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m4_2p8_3p4_4m3_6m4_12p1_24p1_36p2_72m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m4_2p8_3p4_4m3_6m4_12p1_24p1_36p2_72m1 =
    [0, 1, 4, 6, 4, 0, 0, 6, 8, 6, 4, 0, 0, 0, 8, 12, 0, 0, 0, 6,
     8, 0, 8, 0, 0, 5, 0, 6, 0, 0, 0, -6, 0, 0, -4, 0, 0, -2, -8, -12,
     0, 0, 0, -6, -16, -12, -16, 0, 0, -7, -12, -36, -8, 0, 0, -12, -32, 0, -12, 0,
     0, -10, -8, -24, 0, 0, 0, -6, -8, 0, 0, 0, 0, 0, -8, -6, -16, 0, 0, -6,
     0, -18, 12, 0, 0, 14, -24, 12, 0, 0, 0, -12, 32, 0, 0, 0, 0, 0, 4, 24] := by
  eta_coeff

end WeightTwoCusps
