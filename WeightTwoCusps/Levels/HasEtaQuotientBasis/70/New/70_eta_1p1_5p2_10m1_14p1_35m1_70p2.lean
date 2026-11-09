module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 70

The eta expression is `η(z) η(5z)^2 η(10z)^(-1) η(14z) η(35z)^(-1) η(70z)^2`; see
[the local level table](../../TABLE.md#level-70).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z)^2 η(10z)^(-1) η(14z) η(35z)^(-1) η(70z)^2` at level 70. -/
abbrev cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2 : gamma0CuspForms 70 :=
  etaQuotientCuspForm 70 sparse![70; 0 => 1, 4 => 2, 9 => -1, 13 => 1, 34 => -1, 69 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_first_coeffs :
    first_coeffs 100 cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2 =
    [0, 0, 0, 0, 0, 1, -1, -1, 0, 0, -1, 2, 3, 0, 0, -2, 0, -3, 0, -1,
     0, 1, 2, 0, 1, 2, -5, -1, 0, 2, 2, 4, 0, -1, 2, 1, -4, -2, 1, -6,
     -3, 0, -1, 2, -2, 2, 2, 5, 1, 0, -2, 6, -1, -4, 4, -1, 2, 0, -2, -1,
     0, -9, 2, 0, 4, 0, 2, -2, 2, 4, 0, -2, -4, 0, -4, -4, -3, -1, 2, -6,
     2, 4, 6, 3, -1, 4, 6, -1, -2, 8, -1, 1, 2, -2, -4, 2, -7, 1, 0, -2] := by
  eta_coeff

end WeightTwoCusps
