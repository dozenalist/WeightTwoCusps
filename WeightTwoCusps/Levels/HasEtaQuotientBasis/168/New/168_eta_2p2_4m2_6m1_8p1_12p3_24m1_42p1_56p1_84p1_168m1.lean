module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 168

The eta expression is `η(2z)^2 η(4z)^(-2) η(6z)^(-1) η(8z) η(12z)^3 η(24z)^(-1) η(42z) η(56z) η(84z) η(168z)^(-1)`; see
[the local level table](../../TABLE.md#level-168).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(4z)^(-2) η(6z)^(-1) η(8z) η(12z)^3 η(24z)^(-1) η(42z) η(56z) η(84z) η(168z)^(-1)` at level 168. -/
abbrev cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1 : gamma0CuspForms 168 :=
  etaQuotientCuspForm 168 sparse![168; 1 => 2, 3 => -2, 5 => -1, 7 => 1, 11 => 3, 23 => -1, 41 => 1, 55 => 1, 83 => 1, 167 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1_first_coeffs :
    first_coeffs 100 cuspForm_168_eta_2p2_4m2_6m1_8p1_12p3_24m1_42p1_56p1_84p1_168m1 =
    [0, 1, 0, -2, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 0,
     0, 0, 0, -2, 0, -2, 0, 1, 0, -1, 0, -1, 0, 1, 0, 2, 0, 0, 0, 1,
     0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, -4, 0, 2,
     0, -1, 0, 0, 0, -1, 0, 4, 0, -4, 0, 1, 0, 2, 0, -1, 0, -3, 0, 3,
     0, 0, 0, 0, 0, -4, 0, 5, 0, -3, 0, 2, 0, -1, 0, 3, 0, -2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
