module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 135

The eta expression is `η(z)^(-1) η(3z)^3 η(5z)^2 η(15z)^(-1) η(45z)`; see
[the local level table](../../TABLE.md#level-135).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(5z)^2 η(15z)^(-1) η(45z)` at level 135. -/
abbrev cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1 : gamma0CuspForms 135 :=
  etaQuotientCuspForm 135 sparse![135; 0 => -1, 2 => 3, 4 => 2, 14 => -1, 44 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1_first_coeffs :
    first_coeffs 100 cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1 =
    [0, 0, 1, 1, 2, 0, 2, -1, 0, -4, 1, -2, -1, -5, 0, -2, -4, -2, 4, 4,
     -1, 0, 2, 0, -6, 3, 4, 4, -4, 2, -1, 2, -1, 8, 8, 2, 4, -3, 1, -2,
     0, 2, 0, -2, -4, -4, -6, 4, -1, 4, 1, -4, 0, -2, -4, 1, -6, 4, -2, -2,
     2, 4, -3, 0, 0, -2, 4, -7, -1, 0, -3, 2, -12, 1, 2, 1, -6, 0, -4, -10,
     -1, -4, 10, 0, 0, 4, -2, 4, 0, 6, 4, 10, 3, 0, -4, -2, 10, 3, 5, 16] := by
  eta_coeff

end WeightTwoCusps
