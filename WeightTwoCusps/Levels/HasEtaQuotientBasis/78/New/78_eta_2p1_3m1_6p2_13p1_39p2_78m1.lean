module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 78

The eta expression is `η(2z) η(3z)^(-1) η(6z)^2 η(13z) η(39z)^2 η(78z)^(-1)`; see
[the local level table](../../TABLE.md#level-78).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(3z)^(-1) η(6z)^2 η(13z) η(39z)^2 η(78z)^(-1)` at level 78. -/
abbrev cuspForm_78_eta_2p1_3m1_6p2_13p1_39p2_78m1 : gamma0CuspForms 78 :=
  etaQuotientCuspForm 78 sparse![78; 1 => 1, 2 => -1, 5 => 2, 12 => 1, 38 => 2, 77 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_2p1_3m1_6p2_13p1_39p2_78m1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_2p1_3m1_6p2_13p1_39p2_78m1 =
    [0, 1, 0, -1, 1, -1, -1, 0, -1, 0, 1, 1, -1, 0, -1, 1, 1, -1, 2, 2,
     1, 0, 0, -2, 0, 0, 0, -1, -2, 2, -1, 0, 0, -1, 0, -1, 0, -2, 2, 0,
     -3, 1, 1, -3, 1, 3, 0, 5, 1, -2, -4, 3, 0, 4, -1, -4, 5, -4, -6, -3,
     3, 0, 6, 2, 1, 0, 2, 2, -5, 2, -2, -3, 1, -2, 3, 2, 4, -6, 1, 2,
     -3, 3, 0, 5, -2, 2, -8, -2, -4, 3, -4, -1, -2, -2, 5, -4, -1, 4, 2, -9] := by
  eta_coeff

end WeightTwoCusps
