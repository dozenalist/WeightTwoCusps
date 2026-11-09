module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(5z)^2 η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(30z)^2 η(45z)^(-1) η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(5z)^2 η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(30z)^2 η(45z)^(-1) η(90z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p3_3p1_5p2_6m1_9p2_10m2_18m1_30p2_45m1_90p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 3, 2 => 1, 4 => 2, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 29 => 2, 44 => -1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p3_3p1_5p2_6m1_9p2_10m2_18m1_30p2_45m1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p3_3p1_5p2_6m1_9p2_10m2_18m1_30p2_45m1_90p1 =
    [0, 0, 0, 0, 1, 2, 2, 3, 3, 2, 2, 3, 3, 1, 1, 1, -1, 0, 5, 3,
     -1, 2, 0, -4, 0, 4, 0, -3, 4, 4, -2, 5, 6, -5, -9, -2, -10, -15, -1, -2,
     -8, -4, 1, -8, -7, 3, -1, -6, -4, 1, -2, 4, 16, 1, -4, -3, -13, -5, -2, -2,
     -5, -1, 0, 2, 11, 2, 0, -5, -1, 0, -2, 10, 1, -1, 0, 0, -12, -13, -5, -20,
     -5, 2, -10, 3, 2, 0, 0, -4, 0, -12, 4, 7, 5, -4, 9, 4, -10, 19, 3, -10] := by
  eta_coeff

end WeightTwoCusps
