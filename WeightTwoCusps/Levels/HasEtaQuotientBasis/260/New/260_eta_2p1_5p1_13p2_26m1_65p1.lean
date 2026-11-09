module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(2z) η(5z) η(13z)^2 η(26z)^(-1) η(65z)`; see
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

/-- The cuspidal eta quotient `η(2z) η(5z) η(13z)^2 η(26z)^(-1) η(65z)` at level 260. -/
abbrev cuspForm_260_eta_2p1_5p1_13p2_26m1_65p1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 1 => 1, 4 => 1, 12 => 2, 25 => -1, 64 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_2p1_5p1_13p2_26m1_65p1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_2p1_5p1_13p2_26m1_65p1 =
    [0, 0, 0, 1, 0, -1, 0, -1, -1, 0, 1, 0, 1, 0, 0, 1, -2, 2, 1, 0,
     2, 2, -1, -3, 0, -2, 0, -2, -1, 0, -5, 2, 0, -1, 0, 2, 2, 1, 3, 0,
     3, -2, 0, 3, 0, 0, 2, 1, 1, 0, -2, -6, -1, 2, 0, 3, -2, -3, -1, -2,
     -5, -2, 1, -1, 2, 2, 0, 3, -4, 4, 1, 2, 2, 1, -2, -1, 2, -2, 0, -4,
     1, 4, -2, -1, 0, -6, 2, 2, 3, 2, 11, 0, -1, -1, 0, 3, -2, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
