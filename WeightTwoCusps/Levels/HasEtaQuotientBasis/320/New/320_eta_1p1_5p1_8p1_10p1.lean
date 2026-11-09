module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(z) η(5z) η(8z) η(10z)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z) η(8z) η(10z)` at level 320. -/
abbrev cuspForm_320_eta_1p1_5p1_8p1_10p1 : gamma0CuspForms 320 :=
  etaQuotientCuspForm 320 sparse![320; 0 => 1, 4 => 1, 7 => 1, 9 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_320_eta_1p1_5p1_8p1_10p1_first_coeffs :
    first_coeffs 100 cuspForm_320_eta_1p1_5p1_8p1_10p1 =
    [0, 1, -1, -1, 0, 0, 0, 1, 2, -1, 1, -2, 2, 0, 0, -1, -4, -2, -1, 4,
     -2, 2, 0, 3, 0, 1, 6, 2, -6, -2, 0, -2, 0, 0, -2, 1, 4, -4, 0, -6,
     2, 0, -4, -1, 4, 2, 0, 1, 8, 3, -1, -2, 4, 0, 0, -2, -8, 4, 2, 0,
     -2, 0, 0, 1, 0, -2, -8, -3, -8, 6, 0, 6, -6, -2, -2, -1, 8, 8, 0, 4,
     4, -1, 10, -5, -4, -4, 0, -2, 8, -6, 1, 6, -2, -4, 0, 4, 0, -6, 3, -2] := by
  eta_coeff

end WeightTwoCusps
