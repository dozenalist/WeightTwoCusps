module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(18z) η(30z) η(36z)^(-1) η(60z)^(-1) η(90z)^(-1) η(180z)^3`; see
[the local level table](../../TABLE.md#level-180).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(18z) η(30z) η(36z)^(-1) η(60z)^(-1) η(90z)^(-1) η(180z)^3` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p7_3p1_4m2_6m2_12p1_18p1_30p1_36m1_60m1_90m1_180p3 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 17 => 1, 29 => 1, 35 => -1, 59 => -1, 89 => -1, 179 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p7_3p1_4m2_6m2_12p1_18p1_30p1_36m1_60m1_90m1_180p3_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p7_3p1_4m2_6m2_12p1_18p1_30p1_36m1_60m1_90m1_180p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2,
     0, 1, 0, 1, 3, 0, 0, -1, 0, 1, -3, 0, 0, 0, 0, -3, -3, -4, 0, 0,
     0, -3, -6, 0, 0, 0, 0, -3, -6, -2, 0, -2, 0, 1, 0, -2, 0, 0, 0, 2,
     3, 0, 0, 1, 0, 2, 6, 4, 0, 1, 0, 2, 0, 4, 0, 0, 0, -2, 6, 0,
     0, 1, 0, -1, 6, 2, 0, 2, 0, 3, 0, 2, 0, -2, 0, 8, 3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
