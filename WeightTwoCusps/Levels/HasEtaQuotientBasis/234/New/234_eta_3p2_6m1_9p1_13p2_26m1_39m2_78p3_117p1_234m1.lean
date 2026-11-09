module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(3z)^2 η(6z)^(-1) η(9z) η(13z)^2 η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z) η(234z)^(-1)`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^2 η(6z)^(-1) η(9z) η(13z)^2 η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z) η(234z)^(-1)` at level 234. -/
abbrev cuspForm_234_eta_3p2_6m1_9p1_13p2_26m1_39m2_78p3_117p1_234m1 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 2 => 2, 5 => -1, 8 => 1, 12 => 2, 25 => -1, 38 => -2, 77 => 3, 116 => 1, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_3p2_6m1_9p1_13p2_26m1_39m2_78p3_117p1_234m1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_3p2_6m1_9p1_13p2_26m1_39m2_78p3_117p1_234m1 =
    [0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 4, -2, 0, 0, 4, 0,
     -1, 0, 0, 0, 2, 0, 0, -8, 0, -2, 0, 0, -2, 2, 0, 0, 0, 0, 2, 0,
     0, 2, 4, 0, -4, 4, 0, 3, 0, 0, -2, -4, 0, 8, -2, 0, 0, 4, 0, -2,
     -6, 0, 0, 2, 0, 1, -8, 0, -8, 0, 0, -4, 2, 0, -2, 0, 0, 4, -2, 0,
     2, 12, 0, -4, 4, 0, 8, 4, 0, -2, -4, 0, 6, 0, 0, 4, 0, 0, -2, -10] := by
  eta_coeff

end WeightTwoCusps
