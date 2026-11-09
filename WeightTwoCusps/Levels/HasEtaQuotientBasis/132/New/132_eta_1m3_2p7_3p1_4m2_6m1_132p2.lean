module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 132

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(132z)^2`; see
[the local level table](../../TABLE.md#level-132).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(132z)^2` at level 132. -/
abbrev cuspForm_132_eta_1m3_2p7_3p1_4m2_6m1_132p2 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 131 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m3_2p7_3p1_4m2_6m1_132p2_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m3_2p7_3p1_4m2_6m1_132p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, -2,
     0, -2, 0, 0, -6, 0, 0, 1, 0, -4, 0, -4, 0, 0, 0, 0, -3, 4, 0, 0,
     0, 0, 0, -2, 0, -2, 0, 4, 6, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
     3, 6, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 6, 0, 0, 1, 0, 0, 0, -4,
     0, 0, 0, 4, -6, 4, 0, 0, 0, 0, 0, -4, 0, -2, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
