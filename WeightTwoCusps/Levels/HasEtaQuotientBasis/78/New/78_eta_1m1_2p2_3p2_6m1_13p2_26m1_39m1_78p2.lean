module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 78

The eta expression is `η(z)^(-1) η(2z)^2 η(3z)^2 η(6z)^(-1) η(13z)^2 η(26z)^(-1) η(39z)^(-1) η(78z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z)^2 η(6z)^(-1) η(13z)^2 η(26z)^(-1) η(39z)^(-1) η(78z)^2` at level 78. -/
abbrev cuspForm_78_eta_1m1_2p2_3p2_6m1_13p2_26m1_39m1_78p2 : gamma0CuspForms 78 :=
  etaQuotientCuspForm 78 sparse![78; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => 2, 25 => -1, 38 => -1, 77 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m1_2p2_3p2_6m1_13p2_26m1_39m1_78p2_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m1_2p2_3p2_6m1_13p2_26m1_39m1_78p2 =
    [0, 0, 0, 0, 0, 1, 1, 0, -1, -2, 0, -1, 0, 0, -2, 1, 0, 2, -2, -2,
     3, 2, 4, 0, 2, 0, 1, 6, -2, -2, -4, 0, 0, -7, 0, -2, -2, 0, 0, -2,
     -4, 1, 2, 0, -1, 3, 2, -3, 2, 4, 0, 0, 0, -2, 1, 4, 4, 4, -4, 5,
     3, 0, 2, -2, 0, 1, 2, -4, -2, -4, 0, 1, -3, 2, -2, -6, 0, -2, 0, 0,
     -1, -2, 0, -1, 0, -4, -6, -2, 0, 3, 2, 0, 0, 6, 0, 2, 1, 2, 2, 3] := by
  eta_coeff

end WeightTwoCusps
