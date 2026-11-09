module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-3) η(2z)^4 η(3z)^4 η(5z)^3 η(6z)^(-3) η(9z)^(-1) η(10z)^(-2) η(15z)^(-1) η(18z) η(30z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^4 η(3z)^4 η(5z)^3 η(6z)^(-3) η(9z)^(-1) η(10z)^(-2) η(15z)^(-1) η(18z) η(30z)^2` at level 270. -/
abbrev cuspForm_270_eta_1m3_2p4_3p4_5p3_6m3_9m1_10m2_15m1_18p1_30p2 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -3, 1 => 4, 2 => 4, 4 => 3, 5 => -3, 8 => -1, 9 => -2, 14 => -1, 17 => 1, 29 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m3_2p4_3p4_5p3_6m3_9m1_10m2_15m1_18p1_30p2_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m3_2p4_3p4_5p3_6m3_9m1_10m2_15m1_18p1_30p2 =
    [0, 0, 1, 3, 5, 6, 5, 3, -1, -3, -2, 0, 1, 0, 0, -3, 0, 3, 4, -3,
     -10, -9, -13, -3, 4, 9, -2, -6, -3, -6, 2, 0, -1, -21, -13, -6, -7, 0, 4, 3,
     -10, 0, 3, 0, -2, 6, -3, -3, 3, 9, 1, 15, 26, 6, 5, -9, 6, -6, 16, 12,
     -2, 3, -3, 18, -2, 21, 1, -12, -5, 0, 15, 0, 8, 3, 2, 3, 8, -6, -13, -3,
     18, -3, 10, 6, -9, -3, -2, 30, -23, 6, -5, 0, 3, 18, 26, -30, 7, 3, -1, -6] := by
  eta_coeff

end WeightTwoCusps
