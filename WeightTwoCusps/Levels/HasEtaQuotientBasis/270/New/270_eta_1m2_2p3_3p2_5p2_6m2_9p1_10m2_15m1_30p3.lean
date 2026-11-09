module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z)^2 η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z)^2 η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)^3` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p3_3p2_5p2_6m2_9p1_10m2_15m1_30p3 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 3, 2 => 2, 4 => 2, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p3_3p2_5p2_6m2_9p1_10m2_15m1_30p3_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p3_3p2_5p2_6m2_9p1_10m2_15m1_30p3 =
    [0, 0, 0, 1, 2, 2, 2, 1, 0, -1, 0, 1, -1, -2, -2, -2, -1, 4, 4, -1,
     -3, -3, -3, -2, 3, 2, -5, -2, 3, 1, 2, 2, -4, -13, -6, -3, -5, 0, 2, 1,
     -3, 6, 3, -2, 1, 2, -2, -2, 5, 1, 2, 11, 4, 0, -1, -4, 0, -2, 8, 0,
     -1, 3, 2, 6, 2, 7, -5, 0, 4, 0, 6, -2, 0, -3, 0, 1, -1, -2, -7, 3,
     5, -1, 4, -6, -3, -1, 1, 16, -5, 6, 1, 4, -2, 6, 6, -13, 4, -1, 4, -2] := by
  eta_coeff

end WeightTwoCusps
