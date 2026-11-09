module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^2 η(5z)^3 η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(30z) η(45z)^(-1) η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^2 η(5z)^3 η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(30z) η(45z)^(-1) η(90z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p2_5p3_6m1_9p2_10m2_18m1_30p1_45m1_90p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 2, 4 => 3, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 29 => 1, 44 => -1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p2_5p3_6m1_9p2_10m2_18m1_30p1_45m1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p2_5p3_6m1_9p2_10m2_18m1_30p1_45m1_90p1 =
    [0, 0, 0, 1, 2, 3, 4, 5, 5, 4, 5, 6, 5, 3, 4, 2, 0, 3, 6, 4,
     1, 2, 0, -5, 0, 5, -2, -2, 4, 2, -3, 6, 5, -6, -12, -6, -12, -21, -4, -4,
     -14, -8, -2, -12, -12, 2, -2, -12, -5, 0, -4, 0, 18, 5, -8, -5, -12, -10, -4, 2,
     -6, -4, 2, -4, 12, 2, -2, -5, -9, 0, -5, 8, -2, -1, 0, 1, -14, -14, -6, -26,
     -8, 4, -14, 3, 2, -2, -2, 0, 2, -24, 8, 6, 1, -4, 12, 9, -12, 29, 10, -12] := by
  eta_coeff

end WeightTwoCusps
