module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(19z)^(-1) η(38z)^3 η(76z)^(-1) η(114z)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(12z)^2 η(19z)^(-1) η(38z)^3 η(76z)^(-1) η(114z)` at level 228. -/
abbrev cuspForm_228_eta_1m3_2p7_3p2_4m3_6m3_12p2_19m1_38p3_76m1_114p1 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 2, 18 => -1, 37 => 3, 75 => -1, 113 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m3_2p7_3p2_4m3_6m3_12p2_19m1_38p3_76m1_114p1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m3_2p7_3p2_4m3_6m3_12p2_19m1_38p3_76m1_114p1 =
    [0, 0, 0, 0, 0, 0, 1, 3, 2, -1, -1, 1, 3, 1, 0, 2, -2, -2, 0, 0,
     1, -3, 0, 2, -2, 0, 2, 2, 1, -2, 0, 3, -2, 1, 0, -5, -2, -3, 0, 0,
     -1, 0, -1, -2, -2, -3, -1, 6, -1, -5, -4, -5, 1, -4, -2, 0, -6, 0, -1, 4,
     -1, -4, 5, 4, 2, 0, 3, -4, -1, 1, 2, 0, 2, 3, -5, 1, 0, 5, -3, -1,
     5, 1, 6, -2, -2, 0, -4, 4, 4, 2, -1, 0, 4, 0, 5, 0, 2, 4, 4, -2] := by
  eta_coeff

end WeightTwoCusps
