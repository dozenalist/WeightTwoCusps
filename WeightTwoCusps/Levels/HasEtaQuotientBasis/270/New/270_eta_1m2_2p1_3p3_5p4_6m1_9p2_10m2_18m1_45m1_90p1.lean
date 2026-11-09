module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^3 η(5z)^4 η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(45z)^(-1) η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^3 η(5z)^4 η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(45z)^(-1) η(90z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p3_5p4_6m1_9p2_10m2_18m1_45m1_90p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 3, 4 => 4, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 44 => -1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p3_5p4_6m1_9p2_10m2_18m1_45m1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p3_5p4_6m1_9p2_10m2_18m1_45m1_90p1 =
    [0, 0, 1, 2, 4, 5, 8, 8, 9, 8, 12, 10, 10, 8, 10, 4, 4, 7, 12, 4,
     4, 4, 0, -7, 0, 4, -2, -4, 0, 0, -6, 4, 2, -12, -12, -12, -24, -24, -9, -8,
     -24, -14, -4, -16, -26, 4, -4, -20, -10, -4, -7, 0, 8, 11, -16, -8, -16, -20, -8, 8,
     -12, -12, 3, -8, 4, 0, -4, 0, -26, 0, -12, 6, -4, 0, 2, 2, -8, -16, -12, -24,
     -15, 8, -16, 3, 4, -8, -8, 0, 8, -42, 16, -4, -4, -8, 12, 17, -24, 40, 29, -24] := by
  eta_coeff

end WeightTwoCusps
