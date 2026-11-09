module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-1) η(10z)^(-2) η(15z)^(-2) η(30z)^2 η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-1) η(10z)^(-2) η(15z)^(-2) η(30z)^2 η(90z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p3_5p3_6m1_10m2_15m2_30p2_90p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -1, 9 => -2, 14 => -2, 29 => 2, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p3_5p3_6m1_10m2_15m2_30p2_90p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p3_5p3_6m1_10m2_15m2_30p2_90p1 =
    [0, 0, 0, 0, 0, 1, 2, 3, 3, 3, 2, -1, -2, -2, -1, -3, -1, -1, -2, -3,
     0, 3, -1, 2, 1, -2, -7, 0, 1, -1, -1, 2, -5, -12, -4, 0, -1, 0, 7, -3,
     -1, -3, 6, -2, 2, 0, -4, -1, 0, 7, 4, 15, 0, 3, -1, 0, -6, 6, 8, 0,
     -2, 5, 1, -6, 6, 5, 1, -8, 11, 0, 2, -1, 2, -1, -3, 0, -1, -1, -10, 1,
     4, 3, 0, 3, 3, -3, -4, 12, 1, 0, 1, 4, -7, -6, 2, -5, 4, 1, 5, -6] := by
  eta_coeff

end WeightTwoCusps
