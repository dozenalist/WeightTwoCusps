module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^4 η(5z) η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(30z)^3 η(45z)^(-1) η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(5z) η(6z)^(-1) η(9z)^2 η(10z)^(-2) η(18z)^(-1) η(30z)^3 η(45z)^(-1) η(90z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p4_5p1_6m1_9p2_10m2_18m1_30p3_45m1_90p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 4, 4 => 1, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 29 => 3, 44 => -1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p4_5p1_6m1_9p2_10m2_18m1_30p3_45m1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p4_5p1_6m1_9p2_10m2_18m1_30p3_45m1_90p1 =
    [0, 0, 0, 0, 0, 1, 2, 1, 2, 2, -1, 2, 3, -1, 0, 1, -2, -1, 5, 2,
     -2, 2, 0, -3, 0, 3, 0, -3, 4, 4, -2, 4, 6, -5, -6, 0, -10, -9, 0, -2,
     -2, -2, 1, -4, -4, 3, 0, -4, -4, 2, 0, 4, 14, -1, -4, -1, -12, -5, 0, -4,
     -5, 2, 0, 2, 10, 4, 0, -5, 2, 0, 1, 10, 1, -1, 0, 0, -10, -12, -5, -14,
     -4, 2, -6, 3, 2, 2, 0, -4, -2, -6, 4, 8, 6, -4, 6, 1, -10, 9, 0, -10] := by
  eta_coeff

end WeightTwoCusps
