module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-7) η(6z)^(-5) η(8z)^2 η(12z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-7) η(6z)^(-5) η(8z)^2 η(12z)^3` at level 288. -/
abbrev cuspForm_288_eta_1m6_2p15_3p2_4m7_6m5_8p2_12p3 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -6, 1 => 15, 2 => 2, 3 => -7, 5 => -5, 7 => 2, 11 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m6_2p15_3p2_4m7_6m5_8p2_12p3_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m6_2p15_3p2_4m7_6m5_8p2_12p3 =
    [0, 1, 6, 12, 6, -5, 6, 24, 18, 6, 6, 12, 12, 6, 18, 24, 0, -13, 6, 24,
     6, 0, 12, 0, 0, -1, 6, 12, 0, 11, -12, -24, 0, 0, -6, -24, -12, -2, -30, -24,
     0, 7, 0, -24, -12, -12, -24, 24, 0, -7, -24, -72, -12, -1, 6, -48, -72, 0, -18, -12,
     -24, -10, 6, -48, 0, 42, -24, -24, -6, 0, 0, -48, 0, -6, -36, -12, -24, 0, -12, -24,
     0, -18, 18, 36, 0, -4, -42, 24, 0, -29, -12, -48, 24, 0, 0, -24, 0, 18, 30, 48] := by
  eta_coeff

end WeightTwoCusps
