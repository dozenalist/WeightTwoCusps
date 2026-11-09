module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(2z) η(7z)^2 η(8z)`; see
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

/-- The cuspidal eta quotient `η(2z) η(7z)^2 η(8z)` at level 448. -/
abbrev cuspForm_448_eta_2p1_7p2_8p1 : gamma0CuspForms 448 :=
  etaQuotientCuspForm 448 sparse![448; 1 => 1, 6 => 2, 7 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_448_eta_2p1_7p2_8p1_first_coeffs :
    first_coeffs 100 cuspForm_448_eta_2p1_7p2_8p1 =
    [0, 1, 0, -1, 0, -1, 0, 0, -2, -1, 2, 2, 2, 1, 0, 0, 2, 0, -4, 1,
     -2, 1, 0, 0, 0, -3, -2, -2, -2, 0, 0, -2, 6, 0, 4, -1, 4, 0, 0, 4,
     -4, 4, 2, -2, -4, 3, 0, 2, -4, 1, 4, 2, -6, -6, 0, -4, 2, -2, -4, 1,
     0, -1, 0, -2, -6, 2, 0, 0, 12, 0, 0, -4, 6, 6, -4, 1, 6, -2, 0, 4,
     0, -1, -4, 1, -2, 6, 0, 2, 8, -6, 2, 1, 0, -4, 0, 0, -12, -8, 0, 2] := by
  eta_coeff

end WeightTwoCusps
