module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)^2` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p3_5p3_6m2_9p1_10m2_15m1_30p2 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p3_5p3_6m2_9p1_10m2_15m1_30p2_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p3_5p3_6m2_9p1_10m2_15m1_30p2 =
    [0, 0, 1, 2, 3, 3, 3, 2, 0, 0, 1, 1, -2, -2, -3, -3, -1, 4, 4, -2,
     -4, -4, -6, -3, 3, 0, -5, -4, 2, -1, 2, 2, -4, -16, -9, -4, -8, 0, 1, 0,
     -4, 5, 4, -2, 2, 4, -3, -2, 6, 4, 1, 14, 10, 1, 0, -2, 0, 0, 12, 4,
     -1, 4, 0, 8, 2, 10, -4, -4, 8, 0, 8, -1, 4, -2, 5, 2, 1, -3, -10, 2,
     8, 0, 6, -3, -4, -2, 4, 22, -10, 6, 0, 4, -6, 8, 12, -17, 7, 0, 2, -8] := by
  eta_coeff

end WeightTwoCusps
