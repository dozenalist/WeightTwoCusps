module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(z) η(15z) η(20z) η(24z) η(60z)^(-1) η(120z)`; see
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

/-- The cuspidal eta quotient `η(z) η(15z) η(20z) η(24z) η(60z)^(-1) η(120z)` at level 480. -/
abbrev cuspForm_480_eta_1p1_15p1_20p1_24p1_60m1_120p1 : gamma0CuspForms 480 :=
  etaQuotientCuspForm 480 sparse![480; 0 => 1, 14 => 1, 19 => 1, 23 => 1, 59 => -1, 119 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_480_eta_1p1_15p1_20p1_24p1_60m1_120p1_first_coeffs :
    first_coeffs 100 cuspForm_480_eta_1p1_15p1_20p1_24p1_60m1_120p1 =
    [0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0,
     -2, 1, 1, 0, 0, -2, 1, 1, 0, -1, 0, 2, 0, 0, -1, 0, 0, 2, 0, 0,
     0, 0, -3, 0, 2, -2, -1, 2, 0, 2, -1, -2, -2, -1, 2, 1, 0, -1, -1, 0,
     3, -4, 2, 0, 0, 5, 3, -2, 2, 0, 0, -4, 0, 2, -1, -1, 0, -2, 1, -2,
     0, 2, 0, 0, -6, 0, -1, 1, 0, -2, 1, 4, -2, 1, -1, -2, 0, 6, 0, 2] := by
  eta_coeff

end WeightTwoCusps
