module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-1) η(3z)^2 η(4z)^2 η(6z)^(-1) η(13z) η(26z)^(-1) η(39z)^(-1) η(78z)^3 η(117z) η(156z)^(-1) η(234z)^(-1) η(468z)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z)^2 η(6z)^(-1) η(13z) η(26z)^(-1) η(39z)^(-1) η(78z)^3 η(117z) η(156z)^(-1) η(234z)^(-1) η(468z)` at level 468. -/
abbrev cuspForm_468_eta_1m1_3p2_4p2_6m1_13p1_26m1_39m1_78p3_117p1_156m1_234m1_468p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -1, 2 => 2, 3 => 2, 5 => -1, 12 => 1, 25 => -1, 38 => -1, 77 => 3, 116 => 1, 155 => -1, 233 => -1, 467 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m1_3p2_4p2_6m1_13p1_26m1_39m1_78p3_117p1_156m1_234m1_468p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m1_3p2_4p2_6m1_13p1_26m1_39m1_78p3_117p1_156m1_234m1_468p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1,
     1, 1, 1, 3, 1, 1, 0, 1, 2, 1, 1, -1, -1, 1, 0, 0, -2, 1, 1, 0,
     1, -1, -1, 0, 1, 0, -1, 0, 2, -1, -1, 1, 0, 0, 0, -1, -1, -1, 4, 0,
     0, -2, 2, 1, -3, 1, -2, 0, 2, 0, 0, -3, 1, 3, 0, -1, -1, 1, -1, 3,
     0, -2, -2, -3, 0, -2, -3, 0, -2, -1, -1, 0, -3, 1, -3, -1, -3, -2, -1, -3] := by
  eta_coeff

end WeightTwoCusps
