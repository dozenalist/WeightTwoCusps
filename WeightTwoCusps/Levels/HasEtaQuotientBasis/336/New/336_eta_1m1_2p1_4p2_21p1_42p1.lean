module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(z)^(-1) η(2z) η(4z)^2 η(21z) η(42z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^2 η(21z) η(42z)` at level 336. -/
abbrev cuspForm_336_eta_1m1_2p1_4p2_21p1_42p1 : gamma0CuspForms 336 :=
  etaQuotientCuspForm 336 sparse![336; 0 => -1, 1 => 1, 3 => 2, 20 => 1, 41 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_336_eta_1m1_2p1_4p2_21p1_42p1_first_coeffs :
    first_coeffs 100 cuspForm_336_eta_1m1_2p1_4p2_21p1_42p1 =
    [0, 0, 0, 1, 1, 1, 2, 0, 1, 2, 1, 1, 1, 1, 0, 3, 1, 0, 2, 1,
     1, 1, 0, 1, 2, 0, 1, -2, 0, 0, 0, 0, -1, 2, 0, 0, -1, 0, 1, 0,
     -1, 0, -1, 2, 0, -3, -2, -4, -1, 0, -2, -3, -3, -2, -3, -2, 0, -8, -2, 1,
     -2, -1, -2, -2, -1, -2, -6, -2, -2, 2, 1, -1, -5, 0, 2, -5, -1, 0, 2, -2,
     -3, -2, 0, -1, 1, -4, -2, 0, 0, 2, -7, -1, -2, -2, 2, 0, 0, -2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
