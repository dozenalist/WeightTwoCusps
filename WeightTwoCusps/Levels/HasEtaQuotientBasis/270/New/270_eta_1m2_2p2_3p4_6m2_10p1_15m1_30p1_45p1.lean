module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(10z) η(15z)^(-1) η(30z) η(45z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(10z) η(15z)^(-1) η(30z) η(45z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p4_6m2_10p1_15m1_30p1_45p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 9 => 1, 14 => -1, 29 => 1, 44 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p4_6m2_10p1_15m1_30p1_45p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p4_6m2_10p1_15m1_30p1_45p1 =
    [0, 0, 0, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2, 0, -2, 1, 0, 2, 1, 2,
     3, 0, 1, 2, 0, 1, 0, 1, -4, -4, -1, 0, 0, -1, 4, -5, -2, -3, 2, -2,
     -5, 0, -3, -3, -2, -1, -4, -4, -1, 0, -11, -4, -5, 0, -4, -1, 2, -5, -3, 0,
     -1, -2, 0, -6, -4, -12, -2, -1, -2, 0, -5, -4, -3, 1, 0, 1, 0, 2, -1, -4,
     3, 2, 4, 0, 0, -1, 0, 4, 3, 0, 4, 0, 2, 0, -2, 8, -2, 7, -6, -2] := by
  eta_coeff

end WeightTwoCusps
