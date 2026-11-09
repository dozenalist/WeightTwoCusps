module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(2z) η(10z) η(34z) η(170z)`; see
[the local level table](../../TABLE.md#level-340).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(10z) η(34z) η(170z)` at level 340. -/
abbrev cuspForm_340_eta_2p1_10p1_34p1_170p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 1 => 1, 9 => 1, 33 => 1, 169 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_2p1_10p1_34p1_170p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_2p1_10p1_34p1_170p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 2, 0, 0, 0, 0, 0, -2, 0, 1, 0, -1, 0, 0, 0, 0, 0, -2,
     0, 0, 0, -1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 0, -1, 0, -2, 0, 2,
     0, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, 2, 0, 0, 0, -1, 0, 1,
     0, -1, 0, -3, 0, 0, 0, -2, 0, -1, 0, -2, 0, -1, 0, 0, 0, 4, 0, 1] := by
  eta_coeff

end WeightTwoCusps
