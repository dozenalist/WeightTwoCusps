module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(z)^(-1) η(2z) η(4z) η(7z) η(8z) η(28z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z) η(7z) η(8z) η(28z)` at level 448. -/
abbrev cuspForm_448_eta_1m1_2p1_4p1_7p1_8p1_28p1 : gamma0CuspForms 448 :=
  etaQuotientCuspForm 448 sparse![448; 0 => -1, 1 => 1, 3 => 1, 6 => 1, 7 => 1, 27 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_448_eta_1m1_2p1_4p1_7p1_8p1_28p1_first_coeffs :
    first_coeffs 100 cuspForm_448_eta_1m1_2p1_4p1_7p1_8p1_28p1 =
    [0, 0, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2, 1, 4, 3, 1,
     4, 0, 2, 4, 2, 2, 3, 4, 1, 4, 0, 0, 3, 0, 0, 3, -3, 0, 3, -2,
     0, 0, -1, -2, 4, -2, -4, 4, -2, 0, 1, -6, 0, 4, -2, -6, -1, -2, 0, 1,
     -4, -6, 2, -4, -3, -2, -8, 0, -2, -4, -7, 2, -5, -8, 0, -7, -10, 2, -4, -2,
     0, -10, -4, 3, -2, -8, -2, -6, -8, 4, -7, -13, 4, -4, -2, -2, -6, 0, 1, -6] := by
  eta_coeff

end WeightTwoCusps
