module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 135

The eta expression is `η(9z)^2 η(15z)^2`; see
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

/-- The cuspidal eta quotient `η(9z)^2 η(15z)^2` at level 135. -/
abbrev cuspForm_135_eta_9p2_15p2 : gamma0CuspForms 135 :=
  etaQuotientCuspForm 135 sparse![135; 8 => 2, 14 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_135_eta_9p2_15p2_first_coeffs :
    first_coeffs 100 cuspForm_135_eta_9p2_15p2 =
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0,
     -1, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, -1, 0, 0, 2, 0, 0, 1, 0,
     0, 2, 0, 0, -4, 0, 0, 4, 0, 0, 1, 0, 0, -2, 0, 0, -6, 0, 0, -2,
     0, 0, -3, 0, 0, -2, 0, 0, -1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, -2, 0, 0, 6, 0, 0, 3, 0, 0, -2, 0, 0, 5, 0] := by
  eta_coeff

end WeightTwoCusps
