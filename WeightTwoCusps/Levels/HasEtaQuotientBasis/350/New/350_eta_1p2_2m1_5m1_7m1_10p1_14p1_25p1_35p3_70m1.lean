module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(z)^2 η(2z)^(-1) η(5z)^(-1) η(7z)^(-1) η(10z) η(14z) η(25z) η(35z)^3 η(70z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(5z)^(-1) η(7z)^(-1) η(10z) η(14z) η(25z) η(35z)^3 η(70z)^(-1)` at level 350. -/
abbrev cuspForm_350_eta_1p2_2m1_5m1_7m1_10p1_14p1_25p1_35p3_70m1 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 0 => 2, 1 => -1, 4 => -1, 6 => -1, 9 => 1, 13 => 1, 24 => 1, 34 => 3, 69 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_1p2_2m1_5m1_7m1_10p1_14p1_25p1_35p3_70m1_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_1p2_2m1_5m1_7m1_10p1_14p1_25p1_35p3_70m1 =
    [0, 0, 0, 1, -2, 0, 0, 2, 1, -2, 1, -2, 0, 1, 0, 1, -2, 1, 0, -2,
     1, 0, 3, 0, 0, -2, -2, 1, 2, 2, -2, 0, -2, -1, 0, 0, 2, 0, 0, 2,
     -3, 0, -2, 2, 4, -1, 0, -3, 0, 0, 1, 2, 2, -4, 2, -1, 0, -4, -1, 4,
     0, 0, 0, -3, -2, 3, 4, 0, -2, 2, 1, 0, -3, 0, 0, 3, 2, -5, -6, -2,
     3, 4, 2, -2, 2, -1, 4, -3, 0, 0, 1, 2, -1, -2, -4, 0, 4, 1, -4, 0] := by
  eta_coeff

end WeightTwoCusps
