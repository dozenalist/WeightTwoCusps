module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z) η(10z) η(13z) η(65z)^2 η(130z)^(-1)`; see
[the local level table](../../TABLE.md#level-260).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(10z) η(13z) η(65z)^2 η(130z)^(-1)` at level 260. -/
abbrev cuspForm_260_eta_1p1_10p1_13p1_65p2_130m1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => 1, 9 => 1, 12 => 1, 64 => 2, 129 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1p1_10p1_13p1_65p2_130m1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1p1_10p1_13p1_65p2_130m1 =
    [0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, -1, 1, 0, -1, 1, -1, 0, -1, -1,
     0, -2, 1, 3, 1, -1, 0, 0, 0, 3, 0, 1, -1, 0, 0, -1, -3, 0, -1, 0,
     -1, 0, 2, -1, 1, 0, 1, 0, -1, -3, 1, 2, 0, -2, 2, 0, 3, 0, 2, -1,
     1, 1, -1, 0, -2, 0, -1, 2, 0, -1, 0, -3, -3, 0, -1, 1, 3, -2, -1, 4,
     -2, 2, -2, 0, 0, 2, 1, -2, -1, -2, 1, 1, 3, 0, -7, 0, -1, 4, 3, 3] := by
  eta_coeff

end WeightTwoCusps
