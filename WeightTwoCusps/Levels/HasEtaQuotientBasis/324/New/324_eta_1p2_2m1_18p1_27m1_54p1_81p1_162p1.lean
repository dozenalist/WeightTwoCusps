module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(z)^2 η(2z)^(-1) η(18z) η(27z)^(-1) η(54z) η(81z) η(162z)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(18z) η(27z)^(-1) η(54z) η(81z) η(162z)` at level 324. -/
abbrev cuspForm_324_eta_1p2_2m1_18p1_27m1_54p1_81p1_162p1 : gamma0CuspForms 324 :=
  etaQuotientCuspForm 324 sparse![324; 0 => 2, 1 => -1, 17 => 1, 26 => -1, 53 => 1, 80 => 1, 161 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_324_eta_1p2_2m1_18p1_27m1_54p1_81p1_162p1_first_coeffs :
    first_coeffs 100 cuspForm_324_eta_1p2_2m1_18p1_27m1_54p1_81p1_162p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0,
     0, -2, 0, 0, 0, 0, 0, 0, 2, 0, -1, 2, 0, 0, -2, 0, 0, -2, 0, 3,
     -2, 0, 0, 2, 0, 0, -2, 0, -1, 2, 0, 0, -2, 0, 0, 4, 0, 1, 2, 0,
     0, -4, 0, 0, -4, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -1, 4, 0, 0, 0,
     0, 0, 4, 0, -1, 2, 0, 0, -4, 0, 0, -4, 0, -1, -4, 0, 0, 4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
