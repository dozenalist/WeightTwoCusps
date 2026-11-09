module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(15z)^(-1) η(30z)^2 η(135z)^2 η(270z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(15z)^(-1) η(30z)^2 η(135z)^2 η(270z)^(-1)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p4_3p1_6m1_15m1_30p2_135p2_270m1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 14 => -1, 29 => 2, 134 => 2, 269 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p4_3p1_6m1_15m1_30p2_135p2_270m1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p4_3p1_6m1_15m1_30p2_135p2_270m1 =
    [0, 0, 1, 2, 1, 1, 0, -1, 1, 0, 0, -2, -2, 1, -2, 0, -1, 0, 2, 0,
     1, -4, -1, 2, 0, 0, -4, -2, 1, -2, 2, 0, -3, 0, -2, 0, -4, 1, 4, 0,
     0, 0, 0, 0, 2, 2, 0, -2, 6, 0, 1, 0, 1, 6, 0, 1, -2, 0, 2, 2,
     0, -2, -2, 4, -1, 0, -4, 0, 4, 0, 1, -4, 2, 0, 4, 2, 0, -4, 0, 0,
     1, 0, 1, 4, -4, 0, 0, 0, -1, 0, 0, -2, -2, 8, 2, 2, 0, 0, 1, -4] := by
  eta_coeff

end WeightTwoCusps
