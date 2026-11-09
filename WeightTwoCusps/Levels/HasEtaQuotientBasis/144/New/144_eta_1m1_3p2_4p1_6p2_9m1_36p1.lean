module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(6z)^2 η(9z)^(-1) η(36z)`; see
[the local level table](../../TABLE.md#level-144).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(6z)^2 η(9z)^(-1) η(36z)` at level 144. -/
abbrev cuspForm_144_eta_1m1_3p2_4p1_6p2_9m1_36p1 : gamma0CuspForms 144 :=
  etaQuotientCuspForm 144 sparse![144; 0 => -1, 2 => 2, 3 => 1, 5 => 2, 8 => -1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m1_3p2_4p1_6p2_9m1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m1_3p2_4p1_6p2_9m1_36p1 =
    [0, 0, 1, 1, 2, 1, 2, 2, 0, 1, -2, 2, 0, 2, 0, -2, 0, -1, -2, -6,
     0, 0, 4, -4, 0, -2, -2, 1, -8, -3, -4, 6, 0, -4, 2, 0, 0, -8, -4, -2,
     0, 3, 0, -2, 0, -2, -8, 0, 0, 8, -1, 2, 4, 1, 2, -4, 0, 4, 6, 2,
     0, 8, 8, 0, 0, -2, 8, 6, 0, 8, 0, 4, 0, -10, 6, -1, 16, 0, -4, -2,
     0, 1, -6, -2, 0, 2, 4, 6, 0, 3, 4, 4, 0, -8, 0, 4, 0, 6, -7, -4] := by
  eta_coeff

end WeightTwoCusps
