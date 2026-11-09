module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 96

The eta expression is `η(2z) η(6z) η(16z) η(48z)`; see
[the local level table](../../TABLE.md#level-96).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(6z) η(16z) η(48z)` at level 96. -/
abbrev cuspForm_96_eta_2p1_6p1_16p1_48p1 : gamma0CuspForms 96 :=
  etaQuotientCuspForm 96 sparse![96; 1 => 1, 5 => 1, 15 => 1, 47 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_2p1_6p1_16p1_48p1_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_2p1_6p1_16p1_48p1 =
    [0, 0, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 2, 0, -1, 0, 2, 0, -1,
     0, 1, 0, 0, 0, 0, 0, -2, 0, -3, 0, 1, 0, -1, 0, -2, 0, 0, 0, 4,
     0, 2, 0, 1, 0, 1, 0, 2, 0, -4, 0, 0, 0, 1, 0, 2, 0, 1, 0, -1,
     0, -4, 0, -1, 0, -2, 0, 1, 0, 0, 0, -4, 0, 0, 0, -1, 0, 4, 0, 1,
     0, 2, 0, 3, 0, 2, 0, -7, 0, 0, 0, 2, 0, -1, 0, -2, 0, 8, 0, 1] := by
  eta_coeff

end WeightTwoCusps
