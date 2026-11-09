module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(6z)^2 η(10z) η(20z) η(30z)^(-1) η(60z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^2 η(10z) η(20z) η(30z)^(-1) η(60z)` at level 360. -/
abbrev cuspForm_360_eta_6p2_10p1_20p1_30m1_60p1 : gamma0CuspForms 360 :=
  etaQuotientCuspForm 360 sparse![360; 5 => 2, 9 => 1, 19 => 1, 29 => -1, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_360_eta_6p2_10p1_20p1_30m1_60p1_first_coeffs :
    first_coeffs 100 cuspForm_360_eta_6p2_10p1_20p1_30m1_60p1 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, 0, -1, 0, -1, 0, 0, 0, 2,
     0, 2, 0, -2, 0, 1, 0, 1, 0, 4, 0, -2, 0, 4, 0, 2, 0, -1, 0, -6,
     0, -4, 0, -3, 0, -2, 0, -2, 0, 4, 0, 2, 0, -4, 0, 1, 0, 0, 0, 4,
     0, 0, 0, 8, 0, 0, 0, 1, 0, -10, 0, 4, 0, -4, 0, -3, 0, 4, 0, 4,
     0, 4, 0, -2, 0, 1, 0, 2, 0, 0, 0, -2, 0, 8, 0, 0, 0, -2, 0, -8] := by
  eta_coeff

end WeightTwoCusps
