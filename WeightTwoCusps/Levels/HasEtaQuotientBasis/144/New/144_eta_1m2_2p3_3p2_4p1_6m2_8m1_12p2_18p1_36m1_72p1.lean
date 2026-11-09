module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(12z)^2 η(18z) η(36z)^(-1) η(72z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-2) η(8z)^(-1) η(12z)^2 η(18z) η(36z)^(-1) η(72z)` at level 144. -/
abbrev cuspForm_144_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p2_18p1_36m1_72p1 : gamma0CuspForms 144 :=
  etaQuotientCuspForm 144 sparse![144; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 11 => 2, 17 => 1, 35 => -1, 71 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p2_18p1_36m1_72p1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p2_18p1_36m1_72p1 =
    [0, 0, 0, 1, 2, 2, 2, 0, 0, 1, 2, 4, 0, 0, 0, -2, 0, -2, -2, 0,
     0, 0, -4, -8, 0, 0, 0, 1, -8, -6, -4, 0, 0, -4, -2, 0, 0, 0, 0, -2,
     0, 6, 0, 0, 0, -2, 8, 0, 0, 0, 0, 2, 4, 2, 2, 0, 0, 4, -6, 4,
     0, 0, 0, 0, 0, -4, 8, 0, 0, 8, 0, 8, 0, 0, 0, -1, 16, 0, -4, 0,
     0, 1, 6, -4, 0, 0, 0, 6, 0, 6, 4, 0, 0, -8, 0, 8, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
