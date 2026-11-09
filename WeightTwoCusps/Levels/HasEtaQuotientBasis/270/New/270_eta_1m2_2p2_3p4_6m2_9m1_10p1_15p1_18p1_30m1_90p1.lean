module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(9z)^(-1) η(10z) η(15z) η(18z) η(30z)^(-1) η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(9z)^(-1) η(10z) η(15z) η(18z) η(30z)^(-1) η(90z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p4_6m2_9m1_10p1_15p1_18p1_30m1_90p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 8 => -1, 9 => 1, 14 => 1, 17 => 1, 29 => -1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p4_6m2_9m1_10p1_15p1_18p1_30m1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p4_6m2_9m1_10p1_15p1_18p1_30m1_90p1 =
    [0, 0, 0, 0, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3, 2, 1, 3, 1, 4, 1,
     2, -1, -1, 1, -1, -1, -6, 0, -2, -2, -1, -3, 3, -2, -1, -3, -6, 0, -2, 1,
     -1, 0, -2, -3, 2, 0, 1, -8, -4, -3, -7, -2, -7, -3, -6, -2, -2, -2, -3, -6,
     -3, -7, 6, -4, -5, -2, 5, 4, -1, 0, -1, 4, -4, 2, 0, 0, 6, -8, -4, 4,
     -1, 2, -4, 3, -1, -5, -6, 2, 3, 0, 6, -9, 1, 2, -1, 5, -5, 8, 0, -4] := by
  eta_coeff

end WeightTwoCusps
