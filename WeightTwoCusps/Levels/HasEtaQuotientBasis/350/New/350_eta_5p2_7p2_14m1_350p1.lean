module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(5z)^2 η(7z)^2 η(14z)^(-1) η(350z)`; see
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

/-- The cuspidal eta quotient `η(5z)^2 η(7z)^2 η(14z)^(-1) η(350z)` at level 350. -/
abbrev cuspForm_350_eta_5p2_7p2_14m1_350p1 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 4 => 2, 6 => 2, 13 => -1, 349 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_5p2_7p2_14m1_350p1_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_5p2_7p2_14m1_350p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -2, 0, -2, 0, 0, -1, 0, 4, 0, 0, 2, 0, 2, 0, 0, 1, 0, -4, 0, 0,
     2, 0, -2, 2, 0, -2, 0, -4, -4, 0, 0, 0, 4, -2, 0, -2, 0, 0, 4, 0,
     -2, 0, 4, 2, 0, 1, 0, 4, 4, 0, 0, 0, -2, -4, 0, 0, 0, 0, -2, 0,
     2, 0, 0, 0, 0, 3, 0, -4, -2, 0, -2, 0, -6, -2, 0, 2, 0, 4, -2, 0] := by
  eta_coeff

end WeightTwoCusps
