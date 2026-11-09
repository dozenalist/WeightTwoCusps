module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(8z)^2 η(20z)^(-1) η(40z) η(60z) η(120z)`; see
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

/-- The cuspidal eta quotient `η(8z)^2 η(20z)^(-1) η(40z) η(60z) η(120z)` at level 480. -/
abbrev cuspForm_480_eta_8p2_20m1_40p1_60p1_120p1 : gamma0CuspForms 480 :=
  etaQuotientCuspForm 480 sparse![480; 7 => 2, 19 => -1, 39 => 1, 59 => 1, 119 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_480_eta_8p2_20m1_40p1_60p1_120p1_first_coeffs :
    first_coeffs 100 cuspForm_480_eta_8p2_20m1_40p1_60p1_120p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0,
     0, 1, 0, 0, 0, -1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, -4, 0, 0,
     0, 1, 0, 0, 0, -1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0,
     0, -1, 0, 0, 0, -1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
