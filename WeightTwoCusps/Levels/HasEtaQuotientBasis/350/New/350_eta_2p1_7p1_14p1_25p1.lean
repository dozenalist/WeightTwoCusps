module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(2z) η(7z) η(14z) η(25z)`; see
[the local level table](../../TABLE.md#level-350).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(7z) η(14z) η(25z)` at level 350. -/
abbrev cuspForm_350_eta_2p1_7p1_14p1_25p1 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 1 => 1, 6 => 1, 13 => 1, 24 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_2p1_7p1_14p1_25p1_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_2p1_7p1_14p1_25p1 =
    [0, 0, 1, 0, -1, 0, -1, 0, 0, -1, 0, 1, 1, 1, 0, 0, -1, 0, 2, -1,
     2, 0, 0, 0, 0, -1, -3, -2, 0, 1, -2, 1, -1, 2, 1, 0, -1, 2, -1, -1,
     2, -1, 0, -2, 2, -2, 2, 1, -1, 0, 1, 5, 0, -2, 3, 2, 1, 1, -1, 1,
     -2, -4, -4, -1, 1, -4, 3, 1, -5, 2, -2, -2, -1, 1, -2, 0, 0, 1, 2, -5,
     2, 4, 1, -1, 0, 2, 4, -3, 3, 4, 2, 2, -1, 0, -3, 2, -2, -1, 1, 2] := by
  eta_coeff

end WeightTwoCusps
