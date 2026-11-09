module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(15z)^(-2) η(30z) η(45z)^7 η(90z)^(-3) η(135z)^(-2) η(270z)`; see
[the local level table](../../TABLE.md#level-270).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(15z)^(-2) η(30z) η(45z)^7 η(90z)^(-3) η(135z)^(-2) η(270z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p4_3p1_6m1_15m2_30p1_45p7_90m3_135m2_270p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 14 => -2, 29 => 1, 44 => 7, 89 => -3, 134 => -2, 269 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p4_3p1_6m1_15m2_30p1_45p7_90m3_135m2_270p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p4_3p1_6m1_15m2_30p1_45p7_90m3_135m2_270p1 =
    [0, 0, 1, 2, 1, 1, 0, -1, 1, 0, 0, -2, -2, 1, -2, 0, -1, 1, 4, 1,
     2, -4, -2, 3, 0, 0, -6, -4, 2, -4, 2, -1, 0, 8, 1, 4, -8, -3, 9, 0,
     0, -10, -8, 4, -6, 4, -3, -8, 6, -5, 1, -16, 2, 13, 0, 1, -8, 0, 2, 4,
     8, 1, -11, 8, -5, 0, -4, 5, 18, 0, 2, 2, 4, 1, 14, 2, -4, -12, 8, -4,
     -3, 0, 8, 9, -4, 4, 0, 16, -2, 18, 0, 1, 0, 8, 7, 3, 16, -3, 1, -8] := by
  eta_coeff

end WeightTwoCusps
