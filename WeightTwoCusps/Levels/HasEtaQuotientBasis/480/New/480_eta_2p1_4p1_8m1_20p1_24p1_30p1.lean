module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z) η(4z) η(8z)^(-1) η(20z) η(24z) η(30z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(8z)^(-1) η(20z) η(24z) η(30z)` at level 480. -/
abbrev cuspForm_480_eta_2p1_4p1_8m1_20p1_24p1_30p1 : gamma0CuspForms 480 :=
  etaQuotientCuspForm 480 sparse![480; 1 => 1, 3 => 1, 7 => -1, 19 => 1, 23 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_480_eta_2p1_4p1_8m1_20p1_24p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_480_eta_2p1_4p1_8m1_20p1_24p1_30p1 =
    [0, 0, 0, 1, 0, -1, 0, -2, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 2,
     0, -2, 0, -3, 0, 1, 0, 2, 0, -1, 0, 0, 0, -3, 0, 4, 0, -1, 0, -5,
     0, 2, 0, 1, 0, 4, 0, 1, 0, -2, 0, 1, 0, 3, 0, -3, 0, 0, 0, -1,
     0, 0, 0, 2, 0, -5, 0, 5, 0, 1, 0, -8, 0, -2, 0, -2, 0, 0, 0, 2,
     0, 4, 0, 3, 0, -1, 0, -3, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 9] := by
  eta_coeff

end WeightTwoCusps
