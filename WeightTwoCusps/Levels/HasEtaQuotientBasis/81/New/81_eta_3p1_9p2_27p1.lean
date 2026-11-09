module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 81

The eta expression is `η(3z) η(9z)^2 η(27z)`; see
[the local level table](../../TABLE.md#level-81).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(9z)^2 η(27z)` at level 81. -/
abbrev cuspForm_81_eta_3p1_9p2_27p1 : gamma0CuspForms 81 :=
  etaQuotientCuspForm 81 sparse![81; 2 => 1, 8 => 2, 26 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_81_eta_3p1_9p2_27p1_first_coeffs :
    first_coeffs 100 cuspForm_81_eta_3p1_9p2_27p1 =
    [0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -2, 0, 0, 2, 0, 0, 3, 0, 0,
     -1, 0, 0, 2, 0, 0, -1, 0, 0, 1, 0, 0, -3, 0, 0, -2, 0, 0, 2, 0,
     0, -4, 0, 0, -2, 0, 0, 4, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 8,
     0, 0, 8, 0, 0, 1, 0, 0, 3, 0, 0, -6, 0, 0, -7, 0, 0, -4, 0, 0,
     5, 0, 0, -8, 0, 0, 2, 0, 0, -3, 0, 0, 2, 0, 0, -2, 0, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
