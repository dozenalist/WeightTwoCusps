module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(5z)^(-1) η(6z)^(-1) η(9z)^2 η(10z) η(15z)^2 η(18z)^(-1) η(27z)^(-1) η(30z)^(-1) η(45z)^2 η(54z) η(90z)^(-1) η(135z)^(-1) η(270z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(5z)^(-1) η(6z)^(-1) η(9z)^2 η(10z) η(15z)^2 η(18z)^(-1) η(27z)^(-1) η(30z)^(-1) η(45z)^2 η(54z) η(90z)^(-1) η(135z)^(-1) η(270z)` at level 270. -/
abbrev cuspForm_270_eta_1m1_2p1_3p2_5m1_6m1_9p2_10p1_15p2_18m1_27m1_30m1_45p2_54p1_90m1_135m1_270p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -1, 1 => 1, 2 => 2, 4 => -1, 5 => -1, 8 => 2, 9 => 1, 14 => 2, 17 => -1, 26 => -1, 29 => -1, 44 => 2, 53 => 1, 89 => -1, 134 => -1, 269 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m1_2p1_3p2_5m1_6m1_9p2_10p1_15p2_18m1_27m1_30m1_45p2_54p1_90m1_135m1_270p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m1_2p1_3p2_5m1_6m1_9p2_10p1_15p2_18m1_27m1_30m1_45p2_54p1_90m1_135m1_270p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 1, 2, 0, -2, 0, -1, 3,
     0, -4, 0, -4, 2, 0, -4, -1, -6, 2, 0, -4, 2, -2, 3, 1, -1, 1, -3, 4,
     1, -2, -2, -2, 4, 1, 1, 2, -4, 3, 0, -2, -4, -6, 1, 0, -6, -2, -2, -2,
     2, 3, 1, 0, -3, 1, 8, -1, 13, 0, 2, 12, 3, 11, 2, 0, 7, -8, 2, -3,
     -2, 1, 2, 6, -4, 0, 2, 8, 4, -4, -1, -7, -7, 8, -2, 3, 4, 5, 0, -4] := by
  eta_coeff

end WeightTwoCusps
