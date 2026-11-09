module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 78

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z)^3 η(26z)^(-2) η(39z)^(-2) η(78z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z)^3 η(26z)^(-2) η(39z)^(-2) η(78z)^3` at level 78. -/
abbrev cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3 : gamma0CuspForms 78 :=
  etaQuotientCuspForm 78 sparse![78; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 3, 25 => -2, 38 => -2, 77 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3 =
    [0, 0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, -2,
     -8, -5, -6, 2, -1, -1, -3, -6, 10, 6, 7, -2, 0, 12, 0, 11, 1, 0, 4, 2,
     11, -10, -1, 3, 0, -1, -6, 10, -6, -1, 4, -5, 1, -4, 4, -12, -15, 4, 6, -6,
     -11, -2, -6, 3, 4, -1, -8, -4, 13, 4, -10, -6, 3, -2, 3, 5, -10, -4, -1, 6,
     4, -2, 12, 8, 3, 14, 14, 0, 2, -2, -2, 3, 2, -2, -11, -14, 1, 0, -8, -2] := by
  eta_coeff

end WeightTwoCusps
