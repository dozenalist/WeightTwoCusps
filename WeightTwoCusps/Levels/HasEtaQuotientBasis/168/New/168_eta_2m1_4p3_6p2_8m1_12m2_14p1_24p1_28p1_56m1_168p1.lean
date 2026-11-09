module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 168

The eta expression is `η(2z)^(-1) η(4z)^3 η(6z)^2 η(8z)^(-1) η(12z)^(-2) η(14z) η(24z) η(28z) η(56z)^(-1) η(168z)`; see
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

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^3 η(6z)^2 η(8z)^(-1) η(12z)^(-2) η(14z) η(24z) η(28z) η(56z)^(-1) η(168z)` at level 168. -/
abbrev cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1 : gamma0CuspForms 168 :=
  etaQuotientCuspForm 168 sparse![168; 1 => -1, 3 => 3, 5 => 2, 7 => -1, 11 => -2, 13 => 1, 23 => 1, 27 => 1, 55 => -1, 167 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1_first_coeffs :
    first_coeffs 100 cuspForm_168_eta_2m1_4p3_6p2_8m1_12m2_14p1_24p1_28p1_56m1_168p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -2, 0, -2, 0, 1, 0, 1,
     0, -1, 0, 0, 0, -1, 0, 2, 0, 3, 0, 1, 0, 1, 0, -3, 0, -2, 0, 4,
     0, 3, 0, 4, 0, -3, 0, -6, 0, 1, 0, -3, 0, 3, 0, -2, 0, -7, 0, -3,
     0, -2, 0, 3, 0, 1, 0, -2, 0, 2, 0, -1, 0, 0, 0, 9, 0, 3, 0, 5,
     0, -5, 0, -1, 0, 4, 0, 3, 0, 3, 0, -3, 0, 1, 0, -1, 0, -2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
