module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 78

The eta expression is `η(z) η(2z) η(39z) η(78z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(39z) η(78z)` at level 78. -/
abbrev cuspForm_78_eta_1p1_2p1_39p1_78p1 : gamma0CuspForms 78 :=
  etaQuotientCuspForm 78 sparse![78; 0 => 1, 1 => 1, 38 => 1, 77 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p1_2p1_39p1_78p1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p1_2p1_39p1_78p1 =
    [0, 0, 0, 0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2, -2, 0, 2,
     -1, 0, 2, 0, 2, 0, 1, 0, 0, -2, 0, 0, 0, -1, -2, -2, 0, 2, 0, 0,
     -2, 3, 0, 0, 1, 1, 2, 1, 0, 0, -2, -2, 0, 2, -1, 0, 4, 0, -4, -1,
     -1, -4, 2, -2, 0, -1, 0, 0, 2, 0, 2, 1, 1, 2, 2, 0, 0, 2, 0, 4,
     -5, 0, -2, -3, 2, 2, -4, 2, -6, -3, 2, 0, 0, -2, 6, 2, -1, -2, 4, 1] := by
  eta_coeff

end WeightTwoCusps
