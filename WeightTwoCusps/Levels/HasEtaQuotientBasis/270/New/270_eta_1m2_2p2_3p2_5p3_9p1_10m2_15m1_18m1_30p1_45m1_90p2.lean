module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^2 η(5z)^3 η(9z) η(10z)^(-2) η(15z)^(-1) η(18z)^(-1) η(30z) η(45z)^(-1) η(90z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^2 η(5z)^3 η(9z) η(10z)^(-2) η(15z)^(-1) η(18z)^(-1) η(30z) η(45z)^(-1) η(90z)^2` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p2_5p3_9p1_10m2_15m1_18m1_30p1_45m1_90p2 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 2, 4 => 3, 8 => 1, 9 => -2, 14 => -1, 17 => -1, 29 => 1, 44 => -1, 89 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p2_5p3_9p1_10m2_15m1_18m1_30p1_45m1_90p2_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p2_5p3_9p1_10m2_15m1_18m1_30p1_45m1_90p2 =
    [0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 5, 3, 3, 3, 2, 0, 2, 1, -2,
     -1, 1, 1, -2, 3, 2, -4, -3, 4, 0, -1, 6, 4, -7, -8, -2, -8, -12, -3, -1,
     -15, -4, -1, -3, -5, 3, -2, -10, -2, 0, 2, 2, 13, 1, -2, -2, -7, -7, 1, -2,
     -4, 2, 4, -2, 8, 10, -3, -2, -5, 0, -6, 6, 5, -4, 0, 0, -10, -11, -1, -14,
     -7, 4, -6, 3, 1, 1, -4, -2, 1, -12, 2, 6, 1, -2, 10, 2, -11, 8, 5, -14] := by
  eta_coeff

end WeightTwoCusps
