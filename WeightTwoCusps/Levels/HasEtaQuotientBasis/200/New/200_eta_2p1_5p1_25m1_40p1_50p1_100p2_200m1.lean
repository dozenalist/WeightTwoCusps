module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(2z) η(5z) η(25z)^(-1) η(40z) η(50z) η(100z)^2 η(200z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z) η(5z) η(25z)^(-1) η(40z) η(50z) η(100z)^2 η(200z)^(-1)` at level 200. -/
abbrev cuspForm_200_eta_2p1_5p1_25m1_40p1_50p1_100p2_200m1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 1 => 1, 4 => 1, 24 => -1, 39 => 1, 49 => 1, 99 => 2, 199 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_2p1_5p1_25m1_40p1_50p1_100p2_200m1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_2p1_5p1_25m1_40p1_50p1_100p2_200m1 =
    [0, 0, 0, 1, 0, -1, 0, -1, -1, 0, 1, 0, 1, 0, 0, 1, 0, 2, -1, 0,
     0, 0, -1, -1, 0, 0, 0, -2, 2, 0, -2, 0, -1, -2, 0, 1, 0, 2, 3, 0,
     0, 0, 2, -1, 0, 1, 0, 1, 1, 0, -1, 0, -4, 2, 0, -2, 0, -4, -2, 0,
     0, 0, 2, 3, 0, 0, 0, 5, -3, 0, 2, 0, 2, 0, 0, -1, 0, -6, 0, 0,
     0, 0, -3, -5, 0, 2, 0, 4, 3, 0, 1, 0, 6, -2, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
