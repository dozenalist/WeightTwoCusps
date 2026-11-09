module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(z) η(2z) η(5z) η(40z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(5z) η(40z)` at level 320. -/
abbrev cuspForm_320_eta_1p1_2p1_5p1_40p1 : gamma0CuspForms 320 :=
  etaQuotientCuspForm 320 sparse![320; 0 => 1, 1 => 1, 4 => 1, 39 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_320_eta_1p1_2p1_5p1_40p1_first_coeffs :
    first_coeffs 100 cuspForm_320_eta_1p1_2p1_5p1_40p1 =
    [0, 0, 1, -1, -2, 1, 0, 1, 2, 2, -1, -2, -2, -2, 0, -1, 4, -4, 1, 4,
     0, 2, 0, 3, 0, 0, -6, 2, -2, -4, 0, -2, 0, 0, 2, 1, 2, 2, 0, -6,
     2, 6, 4, -1, 4, -1, 0, 1, -8, -6, 1, -2, 0, 6, 0, -2, -8, 4, -2, 0,
     2, -2, 0, 1, 0, 0, 8, -3, 4, 6, 0, 6, -6, 4, 2, -1, 0, -8, 0, 4,
     -4, -10, -10, -5, 4, -2, 0, -2, 8, 0, -1, 6, 10, -4, 0, 4, 0, 8, -3, -2] := by
  eta_coeff

end WeightTwoCusps
