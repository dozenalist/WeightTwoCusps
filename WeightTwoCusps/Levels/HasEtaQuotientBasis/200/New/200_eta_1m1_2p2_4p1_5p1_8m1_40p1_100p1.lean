module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(z)^(-1) η(2z)^2 η(4z) η(5z) η(8z)^(-1) η(40z) η(100z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z) η(5z) η(8z)^(-1) η(40z) η(100z)` at level 200. -/
abbrev cuspForm_200_eta_1m1_2p2_4p1_5p1_8m1_40p1_100p1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 0 => -1, 1 => 2, 3 => 1, 4 => 1, 7 => -1, 39 => 1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m1_2p2_4p1_5p1_8m1_40p1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m1_2p2_4p1_5p1_8m1_40p1_100p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, -2, 0, -1, -1, 1, 0, -2, 0, -2,
     0, 1, 0, 3, 0, 1, -1, -1, 0, 1, 2, 2, 0, -1, 3, -3, 0, 1, 0, 2,
     0, 2, 0, -3, 0, -2, -3, 3, 0, -3, 1, 0, 0, 1, -2, 2, 0, 3, 0, -2,
     0, -2, 0, -1, 0, -2, 0, -4, 0, -1, -2, 2, 0, 4, -1, -1, 0, -2, 0, 4,
     0, -5, 0, -2, 0, 4, 5, -2, 0, 3, -1, 0, 0, 2, 3, 4, 0, 1, 0, 2] := by
  eta_coeff

end WeightTwoCusps
