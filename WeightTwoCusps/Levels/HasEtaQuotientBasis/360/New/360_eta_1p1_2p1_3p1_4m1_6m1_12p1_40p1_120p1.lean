module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(z) η(2z) η(3z) η(4z)^(-1) η(6z)^(-1) η(12z) η(40z) η(120z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(3z) η(4z)^(-1) η(6z)^(-1) η(12z) η(40z) η(120z)` at level 360. -/
abbrev cuspForm_360_eta_1p1_2p1_3p1_4m1_6m1_12p1_40p1_120p1 : gamma0CuspForms 360 :=
  etaQuotientCuspForm 360 sparse![360; 0 => 1, 1 => 1, 2 => 1, 3 => -1, 5 => -1, 11 => 1, 39 => 1, 119 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_360_eta_1p1_2p1_3p1_4m1_6m1_12p1_40p1_120p1_first_coeffs :
    first_coeffs 100 cuspForm_360_eta_1p1_2p1_3p1_4m1_6m1_12p1_40p1_120p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 0, 2, 3, -2, 0, 1, -2, -2, 0, 2,
     0, -2, 0, 3, -2, 0, 0, 2, 3, -2, 0, 2, -2, -2, 0, 0, 0, -4, 0, 2,
     -1, -2, 0, 2, 6, 0, 0, 0, -1, 0, 0, 2, -3, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, -3, 2, 0, 0, -1, 0, 0, 0, 6, 2, 0, 2,
     1, 0, 0, 0, -6, 0, 0, 0, 1, 0, 0, -6, 0, 0, 0, -1, 2, 2, 0, -2] := by
  eta_coeff

end WeightTwoCusps
