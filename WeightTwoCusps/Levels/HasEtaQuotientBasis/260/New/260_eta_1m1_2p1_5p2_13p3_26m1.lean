module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-1) η(2z) η(5z)^2 η(13z)^3 η(26z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^2 η(13z)^3 η(26z)^(-1)` at level 260. -/
abbrev cuspForm_260_eta_1m1_2p1_5p2_13p3_26m1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -1, 1 => 1, 4 => 2, 12 => 3, 25 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m1_2p1_5p2_13p3_26m1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m1_2p1_5p2_13p3_26m1 =
    [0, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3, 3, 4, 1, 1, 3, 0, -1, 5,
     0, -2, 3, -3, -1, 1, 0, 0, 2, -3, -2, 3, -7, 0, 0, -5, -3, 2, -3, -8,
     1, -6, -6, 1, -5, -4, -1, -2, -7, 1, -9, -10, 0, -10, -2, 4, -7, -8, 2, -7,
     -5, 3, -3, -8, 4, -4, -3, -2, -4, -3, 2, -1, -7, 4, -3, -3, 7, -2, 1, 4,
     -4, 0, 10, 0, -8, 4, -13, -2, 1, 2, -3, 5, 5, 0, -1, -4, 7, 4, 3, 5] := by
  eta_coeff

end WeightTwoCusps
