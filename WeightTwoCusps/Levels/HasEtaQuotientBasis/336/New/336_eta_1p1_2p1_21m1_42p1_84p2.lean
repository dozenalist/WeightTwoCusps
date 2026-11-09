module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(z) η(2z) η(21z)^(-1) η(42z) η(84z)^2`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(21z)^(-1) η(42z) η(84z)^2` at level 336. -/
abbrev cuspForm_336_eta_1p1_2p1_21m1_42p1_84p2 : gamma0CuspForms 336 :=
  etaQuotientCuspForm 336 sparse![336; 0 => 1, 1 => 1, 20 => -1, 41 => 1, 83 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_336_eta_1p1_2p1_21m1_42p1_84p2_first_coeffs :
    first_coeffs 100 cuspForm_336_eta_1p1_2p1_21m1_42p1_84p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2,
     -2, 0, 2, -1, 0, 2, 0, 2, 0, 2, -1, -2, -1, 0, 2, 1, -1, -2, -4, 1,
     0, -2, 0, 0, 2, 0, 2, 2, 2, 0, 4, -1, 0, -2, -2, 2, 1, -1, -4, -2,
     1, -2, -4, -1, -2, 4, 0, 2, 2, 2, 0, 5, -2, 0, 0, -2, 4, 2, -1, -2,
     -2, 2, -2, -8, -1, -2, 4, 0, 2, 2, 6, 0, 2, 0, 4, -8, -2, 0, 0, -3] := by
  eta_coeff

end WeightTwoCusps
