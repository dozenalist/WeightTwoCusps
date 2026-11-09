module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(z) η(4z)^(-1) η(8z) η(12z) η(15z) η(40z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(4z)^(-1) η(8z) η(12z) η(15z) η(40z)` at level 480. -/
abbrev cuspForm_480_eta_1p1_4m1_8p1_12p1_15p1_40p1 : gamma0CuspForms 480 :=
  etaQuotientCuspForm 480 sparse![480; 0 => 1, 3 => -1, 7 => 1, 11 => 1, 14 => 1, 39 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_480_eta_1p1_4m1_8p1_12p1_15p1_40p1_first_coeffs :
    first_coeffs 100 cuspForm_480_eta_1p1_4m1_8p1_12p1_15p1_40p1 =
    [0, 0, 0, 1, -1, -1, 0, 1, 0, -1, 1, 1, 0, -1, 1, 0, 0, -1, -1, 1,
     1, -1, -1, 1, 0, -2, -1, 0, 2, 0, 1, 1, 0, -1, 1, 1, 1, -1, -2, 3,
     0, -1, 0, -1, -2, 0, -2, 1, 0, 1, -1, 0, 0, 1, 0, 0, 0, 2, -1, -1,
     -2, 1, 2, -1, 0, 2, 1, 1, 0, -1, 1, -2, 0, 2, 1, -2, 0, 0, 1, -5,
     0, 1, 0, -3, 0, 4, 4, -6, 0, 2, 0, -2, 0, 2, 0, -1, 0, 0, 4, -3] := by
  eta_coeff

end WeightTwoCusps
