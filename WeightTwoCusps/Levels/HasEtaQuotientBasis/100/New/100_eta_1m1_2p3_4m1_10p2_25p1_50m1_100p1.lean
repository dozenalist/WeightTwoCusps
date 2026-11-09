module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 100

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(10z)^2 η(25z) η(50z)^(-1) η(100z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(10z)^2 η(25z) η(50z)^(-1) η(100z)` at level 100. -/
abbrev cuspForm_100_eta_1m1_2p3_4m1_10p2_25p1_50m1_100p1 : gamma0CuspForms 100 :=
  etaQuotientCuspForm 100 sparse![100; 0 => -1, 1 => 3, 3 => -1, 9 => 2, 24 => 1, 49 => -1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_100_eta_1m1_2p3_4m1_10p2_25p1_50m1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_100_eta_1m1_2p3_4m1_10p2_25p1_50m1_100p1 =
    [0, 0, 0, 0, 1, 1, -1, 0, 0, -1, 0, -1, 0, 0, -2, -2, 1, 0, 0, 3,
     0, 2, 0, 0, -1, -1, 4, 0, 0, -2, 0, 2, 0, 0, 3, 2, -2, 0, 0, 0,
     0, -3, 0, 0, -3, 1, -6, 0, 0, 0, 0, -5, 0, 0, 5, 0, -2, 0, 0, -4,
     0, 0, 0, 0, 1, 2, 3, 0, 0, 6, 0, 8, 0, 0, -2, 2, 5, 0, 0, -6,
     0, 4, 0, 0, 2, -6, 4, 0, 0, 7, 0, -4, 0, 0, -12, -4, -1, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
