module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(z)^(-1) η(2z)^2 η(5z) η(10z)^(-1) η(20z)^3 η(40z)^(-1) η(50z) η(100z)^(-1) η(200z)`; see
[the local level table](../../TABLE.md#level-200).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(5z) η(10z)^(-1) η(20z)^3 η(40z)^(-1) η(50z) η(100z)^(-1) η(200z)` at level 200. -/
abbrev cuspForm_200_eta_1m1_2p2_5p1_10m1_20p3_40m1_50p1_100m1_200p1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 19 => 3, 39 => -1, 49 => 1, 99 => -1, 199 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m1_2p2_5p1_10m1_20p3_40m1_50p1_100m1_200p1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m1_2p2_5p1_10m1_20p3_40m1_50p1_100m1_200p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, 0, 0, -1, 0, 1, -1, 0,
     0, 0, -1, -1, 0, -1, 0, -3, -2, 0, -2, 0, 1, -1, 0, 3, 0, -2, 3, 0,
     0, 0, 2, 3, 0, 2, 0, 3, -1, 0, -1, 0, 4, 2, 0, -2, 0, -1, -2, 0,
     0, 0, 2, -1, 0, 2, 0, -4, 3, 0, 2, 0, -2, 3, 0, 1, 0, 2, 0, 0,
     0, 0, -3, -2, 0, -4, 0, 6, -3, 0, 1, 0, -6, -6, 0, -4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
