module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 100

The eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z)^2 η(20z)^2 η(25z)^(-1) η(50z)^2 η(100z)^(-1)`; see
[the local level table](../../TABLE.md#level-100).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z)^2 η(20z)^2 η(25z)^(-1) η(50z)^2 η(100z)^(-1)` at level 100. -/
abbrev cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1 : gamma0CuspForms 100 :=
  etaQuotientCuspForm 100 sparse![100; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 19 => 2, 24 => -1, 49 => 2, 99 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1_first_coeffs :
    first_coeffs 100 cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1 =
    [0, 1, 1, 0, 1, 1, -1, -1, 1, 0, 0, -1, -1, 1, -2, -2, 1, 2, -2, -1,
     0, -2, -3, -3, -1, -1, 4, 1, -2, 4, 0, -2, 1, 1, 3, 2, -2, -1, 5, -4,
     0, 3, 2, 3, -3, 1, -6, -3, -1, -3, 0, 7, 4, -1, 5, 0, -2, -3, 0, 8,
     0, 2, 2, 1, 1, 2, 3, 4, 3, -6, 0, -4, -2, -4, -2, 2, 5, 2, -4, 2,
     0, -7, -3, 2, 2, -6, 4, 2, -3, 1, 0, 0, -6, -2, -12, -4, -1, -1, -3, 2] := by
  eta_coeff

end WeightTwoCusps
