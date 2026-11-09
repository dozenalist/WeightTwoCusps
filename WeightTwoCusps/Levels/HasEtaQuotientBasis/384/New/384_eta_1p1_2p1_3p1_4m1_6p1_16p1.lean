module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(z) η(2z) η(3z) η(4z)^(-1) η(6z) η(16z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(3z) η(4z)^(-1) η(6z) η(16z)` at level 384. -/
abbrev cuspForm_384_eta_1p1_2p1_3p1_4m1_6p1_16p1 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 0 => 1, 1 => 1, 2 => 1, 3 => -1, 5 => 1, 15 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_1p1_2p1_3p1_4m1_6p1_16p1_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_1p1_2p1_3p1_4m1_6p1_16p1 =
    [0, 1, -1, -2, 0, 2, 3, -4, 2, 5, -2, -6, -6, 6, 0, -4, 4, 6, -1, -2,
     0, 4, 0, -4, 2, -1, -2, -4, 0, 2, 6, -8, 0, 0, -2, 0, 0, 6, 0, 4,
     -4, 2, 0, 10, 0, -6, 0, 8, -4, -7, 1, -4, 0, -14, -9, 4, 0, 0, 6, 2,
     12, -2, 0, 12, 0, -4, 4, 6, 0, -8, 0, 4, 2, -18, 6, 10, 0, -8, -18, 0,
     -8, -3, 6, 14, 0, -4, 0, 12, -8, -2, -2, 8, 0, -12, 0, 12, 0, -2, 7, 2] := by
  eta_coeff

end WeightTwoCusps
