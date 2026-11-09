module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(2z) η(4z) η(6z)^(-1) η(12z) η(30z)^2`; see
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

/-- The cuspidal eta quotient `η(2z) η(4z) η(6z)^(-1) η(12z) η(30z)^2` at level 360. -/
abbrev cuspForm_360_eta_2p1_4p1_6m1_12p1_30p2 : gamma0CuspForms 360 :=
  etaQuotientCuspForm 360 sparse![360; 1 => 1, 3 => 1, 5 => -1, 11 => 1, 29 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_360_eta_2p1_4p1_6m1_12p1_30p2_first_coeffs :
    first_coeffs 100 cuspForm_360_eta_2p1_4p1_6m1_12p1_30p2 =
    [0, 0, 0, 1, 0, -1, 0, -2, 0, 2, 0, -1, 0, 0, 0, 3, 0, -1, 0, 0,
     0, 2, 0, -1, 0, -4, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 4, 0, -2,
     0, 2, 0, -2, 0, -2, 0, 1, 0, 0, 0, -2, 0, 1, 0, 8, 0, 0, 0, 1,
     0, -4, 0, -4, 0, 3, 0, 2, 0, -6, 0, 0, 0, 4, 0, -7, 0, 2, 0, -4,
     0, -4, 0, 3, 0, 4, 0, -2, 0, 2, 0, 8, 0, 0, 0, 2, 0, -4, 0, 4] := by
  eta_coeff

end WeightTwoCusps
