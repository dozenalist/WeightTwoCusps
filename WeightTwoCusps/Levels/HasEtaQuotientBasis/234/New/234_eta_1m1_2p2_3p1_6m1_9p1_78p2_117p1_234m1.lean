module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(9z) η(78z)^2 η(117z) η(234z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(9z) η(78z)^2 η(117z) η(234z)^(-1)` at level 234. -/
abbrev cuspForm_234_eta_1m1_2p2_3p1_6m1_9p1_78p2_117p1_234m1 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 8 => 1, 77 => 2, 116 => 1, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m1_2p2_3p1_6m1_9p1_78p2_117p1_234m1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m1_2p2_3p1_6m1_9p1_78p2_117p1_234m1 =
    [0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, -3, -1, 0, 0, 1, 0, 0, -1, 0,
     1, -1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0,
     0, 0, 0, 0, 0, -1, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0,
     -1, 0, 0, -1, 0, 1, 0, 0, 0, -2, 0, 0, 1, 0, -2, 1, 0, 0, 0, 0,
     -2, -3, 0, 0, 3, 0, 0, 0, 0, 6, 3, 0, 2, -2, 0, 0, 3, 0, -2, 2] := by
  eta_coeff

end WeightTwoCusps
