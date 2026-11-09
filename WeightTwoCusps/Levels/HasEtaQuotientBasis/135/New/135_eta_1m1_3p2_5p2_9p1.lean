module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 135

The eta expression is `η(z)^(-1) η(3z)^2 η(5z)^2 η(9z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(5z)^2 η(9z)` at level 135. -/
abbrev cuspForm_135_eta_1m1_3p2_5p2_9p1 : gamma0CuspForms 135 :=
  etaQuotientCuspForm 135 sparse![135; 0 => -1, 2 => 2, 4 => 2, 8 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_135_eta_1m1_3p2_5p2_9p1_first_coeffs :
    first_coeffs 100 cuspForm_135_eta_1m1_3p2_5p2_9p1 =
    [0, 1, 1, 2, 1, 3, 1, 2, 0, 4, 0, 1, -2, 2, -3, -1, -2, 4, -4, -1,
     -4, 0, -6, -3, -3, 1, -5, -4, -4, -1, -2, -1, -4, 4, -6, -4, -4, 2, 1, -4,
     -3, 5, 0, -4, 2, 4, 0, -2, -2, 9, 1, -2, 8, 1, 4, 0, 0, 8, 6, 4,
     1, 5, 0, 0, 1, 10, 8, -10, 8, 0, 6, -1, 12, 8, 5, 2, 5, -3, -2, -7,
     8, 4, 6, -3, 0, -3, 4, 2, 0, 6, -4, -8, -6, 0, 12, -17, 5, 8, 2, -16] := by
  eta_coeff

end WeightTwoCusps
