module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(7z) η(10z)^(-1) η(35z)^(-1) η(70z) η(175z)^2 η(350z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(7z) η(10z)^(-1) η(35z)^(-1) η(70z) η(175z)^2 η(350z)^(-1)` at level 350. -/
abbrev cuspForm_350_eta_1m1_2p1_5p3_7p1_10m1_35m1_70p1_175p2_350m1 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 0 => -1, 1 => 1, 4 => 3, 6 => 1, 9 => -1, 34 => -1, 69 => 1, 174 => 2, 349 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_1m1_2p1_5p3_7p1_10m1_35m1_70p1_175p2_350m1_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_1m1_2p1_5p3_7p1_10m1_35m1_70p1_175p2_350m1 =
    [0, 0, 1, 1, 1, 2, 2, 0, 1, 1, -1, 1, 0, -1, 1, 1, -3, 1, -1, -4,
     -1, -1, -2, 0, 0, -4, 0, -1, -1, -1, 0, -2, -1, -1, -4, 0, -1, -2, 0, 3,
     3, 4, 0, -2, 4, -3, 0, 1, 0, 2, 3, -3, 0, 2, -6, -1, -1, 2, 0, 2,
     -2, 2, 2, 1, -3, -1, 2, 0, 2, -2, -1, 0, 1, 0, 4, 7, 4, -1, 0, 7,
     1, -2, 0, 2, 2, 5, -2, -1, 0, -6, -1, -1, 2, 2, 6, -2, 4, 1, 1, -4] := by
  eta_coeff

end WeightTwoCusps
