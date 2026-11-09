module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z)^(-1) η(2z) η(5z)^2 η(6z) η(10z)^(-1) η(15z) η(50z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^2 η(6z) η(10z)^(-1) η(15z) η(50z)` at level 450. -/
abbrev cuspForm_450_eta_1m1_2p1_5p2_6p1_10m1_15p1_50p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => -1, 1 => 1, 4 => 2, 5 => 1, 9 => -1, 14 => 1, 49 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1m1_2p1_5p2_6p1_10m1_15p1_50p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1m1_2p1_5p2_6p1_10m1_15p1_50p1 =
    [0, 0, 0, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 0, 1,
     2, 1, -1, 3, 2, 1, 3, 1, 2, 0, 1, 1, 1, 3, 2, 0, -1, 2, -1, 0,
     0, 0, 1, -1, -1, 1, 2, 0, 1, 0, -1, -1, 1, -3, 1, -1, -3, -4, -2, 0,
     -2, -1, -5, -4, -7, -2, -2, -4, 1, -2, -3, -3, 1, -4, -4, -1, -7, -3, -6, -1,
     -1, -1, -2, -3, -7, -4, 0, -3, 1, 0, -4, -1, 0, -1, 3, -5, -4, -4, -1, -2] := by
  eta_coeff

end WeightTwoCusps
