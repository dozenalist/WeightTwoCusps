module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 176

The eta expression is `η(2z) η(8z) η(22z) η(88z)`; see
[the local level table](../../TABLE.md#level-176).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(8z) η(22z) η(88z)` at level 176. -/
abbrev cuspForm_176_eta_2p1_8p1_22p1_88p1 : gamma0CuspForms 176 :=
  etaQuotientCuspForm 176 sparse![176; 1 => 1, 7 => 1, 21 => 1, 87 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_2p1_8p1_22p1_88p1_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_2p1_8p1_22p1_88p1 =
    [0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 2, 0, 1, 0, 1,
     0, -1, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1,
     0, -1, 0, 2, 0, 2, 0, -2, 0, 0, 0, 3, 0, 2, 0, 1, 0, 3, 0, -2,
     0, 0, 0, -2, 0, -3, 0, -2, 0, -1, 0, 2, 0, -1, 0, 0, 0, -1, 0, 2,
     0, -2, 0, 0, 0, -1, 0, 2, 0, -1, 0, 2, 0, -1, 0, 1, 0, 3, 0, -1] := by
  eta_coeff

end WeightTwoCusps
