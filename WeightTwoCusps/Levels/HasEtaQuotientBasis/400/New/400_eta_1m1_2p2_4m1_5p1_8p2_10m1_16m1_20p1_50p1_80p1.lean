module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z)^2 η(10z)^(-1) η(16z)^(-1) η(20z) η(50z) η(80z)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z)^2 η(10z)^(-1) η(16z)^(-1) η(20z) η(50z) η(80z)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p2_4m1_5p1_8p2_10m1_16m1_20p1_50p1_80p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 2, 9 => -1, 15 => -1, 19 => 1, 49 => 1, 79 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p2_4m1_5p1_8p2_10m1_16m1_20p1_50p1_80p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p2_4m1_5p1_8p2_10m1_16m1_20p1_50p1_80p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, -1, -1, 1, -1, 0, 1,
     1, -1, 0, 0, -1, 0, -2, 0, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0, 1,
     0, 1, 0, -1, -1, 0, 1, -2, 0, -1, 0, 0, 0, -2, 0, 2, -2, 0, 0, -2,
     -2, 1, 0, -1, 1, 0, 0, 1, 0, -1, -1, 3, 0, 2, 2, 1, 3, 1, 0, -2,
     0, -1, 0, 3, 2, 0, -1, -1, 0, -2, -1, -1, 0, 1, 3, 0, -1, 4, 0, -1] := by
  eta_coeff

end WeightTwoCusps
