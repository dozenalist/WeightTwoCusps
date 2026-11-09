module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-4) η(6z)^(-4) η(8z)^2 η(12z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-4) η(6z)^(-4) η(8z)^2 η(12z)^2` at level 288. -/
abbrev cuspForm_288_eta_1m4_2p8_3p4_4m4_6m4_8p2_12p2 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -4, 1 => 8, 2 => 4, 3 => -4, 5 => -4, 7 => 2, 11 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m4_2p8_3p4_4m4_6m4_8p2_12p2_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m4_2p8_3p4_4m4_6m4_8p2_12p2 =
    [0, 1, 4, 6, 4, 1, 4, 12, 12, 6, 4, 6, 8, 6, 12, 12, 0, -1, 4, 12,
     4, 0, 8, 0, 0, -1, 4, 6, 0, 5, -8, -12, 0, 0, -4, -12, -8, -2, -20, -12,
     0, -5, 0, -12, -8, -12, -16, 12, 0, -7, -16, -36, -8, -7, 4, -24, -48, 0, -12, -6,
     -16, -10, 4, -24, 0, 6, -16, -12, -4, 0, 0, -24, 0, -6, -24, -6, -16, 0, -8, -12,
     0, -18, 12, 18, 0, -4, -28, 12, 0, -5, -8, -24, 16, 0, 0, -12, 0, 18, 20, 24] := by
  eta_coeff

end WeightTwoCusps
