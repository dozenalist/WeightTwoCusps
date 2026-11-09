module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 220

The eta expression is `η(z) η(20z) η(44z) η(55z)`; see
[the local level table](../../TABLE.md#level-220).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(20z) η(44z) η(55z)` at level 220. -/
abbrev cuspForm_220_eta_1p1_20p1_44p1_55p1 : gamma0CuspForms 220 :=
  etaQuotientCuspForm 220 sparse![220; 0 => 1, 19 => 1, 43 => 1, 54 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_220_eta_1p1_20p1_44p1_55p1_first_coeffs :
    first_coeffs 100 cuspForm_220_eta_1p1_20p1_44p1_55p1 =
    [0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0,
     -1, 0, 0, 0, 0, -1, 1, 2, 0, 0, -1, 1, -1, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 0, 0, -2, 1, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 1, 0, 0,
     1, 2, 2, 0, 1, 0, 0, -2, 0, 1, -1, -3, 1, 0, 1, -1, 0, 0, 0, 0,
     2, -2, -4, 0, 0, 2, -1, 1, 0, 2, -1, 0, -1, -1, 2, 3, 0, 1, -1, 0] := by
  eta_coeff

end WeightTwoCusps
