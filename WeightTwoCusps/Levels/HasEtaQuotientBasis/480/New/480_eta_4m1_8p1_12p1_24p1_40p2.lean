module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(4z)^(-1) η(8z) η(12z) η(24z) η(40z)^2`; see
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

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z) η(12z) η(24z) η(40z)^2` at level 480. -/
abbrev cuspForm_480_eta_4m1_8p1_12p1_24p1_40p2 : gamma0CuspForms 480 :=
  etaQuotientCuspForm 480 sparse![480; 3 => -1, 7 => 1, 11 => 1, 23 => 1, 39 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_480_eta_4m1_8p1_12p1_24p1_40p2_first_coeffs :
    first_coeffs 100 cuspForm_480_eta_4m1_8p1_12p1_24p1_40p2 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
     0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0,
     0, -1, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
