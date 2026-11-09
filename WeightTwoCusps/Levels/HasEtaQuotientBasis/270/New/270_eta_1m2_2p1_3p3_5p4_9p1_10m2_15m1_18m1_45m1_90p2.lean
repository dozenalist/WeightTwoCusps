module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^3 η(5z)^4 η(9z) η(10z)^(-2) η(15z)^(-1) η(18z)^(-1) η(45z)^(-1) η(90z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^3 η(5z)^4 η(9z) η(10z)^(-2) η(15z)^(-1) η(18z)^(-1) η(45z)^(-1) η(90z)^2` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p3_5p4_9p1_10m2_15m1_18m1_45m1_90p2 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 3, 4 => 4, 8 => 1, 9 => -2, 14 => -1, 17 => -1, 44 => -1, 89 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p3_5p4_9p1_10m2_15m1_18m1_45m1_90p2_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p3_5p4_9p1_10m2_15m1_18m1_45m1_90p2 =
    [0, 0, 0, 0, 0, 1, 2, 4, 5, 8, 8, 8, 6, 8, 6, 4, 4, 5, 2, -4,
     1, 2, 0, -3, 6, 0, -6, -6, 4, -2, -2, 4, 3, -14, -12, -6, -16, -12, -6, -2,
     -20, -8, -2, -4, -10, 6, 0, -16, -4, -4, 0, 4, 8, 5, -4, -4, -6, -14, 0, 2,
     -8, -4, 6, -4, 4, 10, -6, 4, -13, 0, -8, 4, 10, -4, 0, 0, -4, -12, -2, -8,
     -10, 8, -12, 3, 2, -4, -6, -4, 4, -24, 4, -4, -3, -4, 12, 7, -22, 12, 12, -28] := by
  eta_coeff

end WeightTwoCusps
