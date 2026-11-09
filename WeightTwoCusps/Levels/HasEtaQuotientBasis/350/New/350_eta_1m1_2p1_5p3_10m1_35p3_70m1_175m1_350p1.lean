module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-1) η(35z)^3 η(70z)^(-1) η(175z)^(-1) η(350z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-1) η(35z)^3 η(70z)^(-1) η(175z)^(-1) η(350z)` at level 350. -/
abbrev cuspForm_350_eta_1m1_2p1_5p3_10m1_35p3_70m1_175m1_350p1 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 34 => 3, 69 => -1, 174 => -1, 349 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_1m1_2p1_5p3_10m1_35p3_70m1_175m1_350p1_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_1m1_2p1_5p3_10m1_35p3_70m1_175m1_350p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 0, 1, 2, 0, 2, 2,
     1, 1, 2, 0, 2, 2, 0, 2, 0, 1, 2, 2, 0, 2, 2, 0, 2, 2, 2, 1,
     1, 0, 0, 2, -3, -1, -1, -4, -4, 0, -3, -3, 2, -6, -4, -1, -3, -4, 2, -6,
     -4, 0, -6, 0, 1, -5, -4, 2, -6, -4, 1, -6, -6, -4, -1, -1, 2, 0, -4, 3,
     -5, -2, -2, -4, 0, 3, -7, -4, 4, -4, -3, 1, -2, -4, 2, -4, 2, 4, 0, -10] := by
  eta_coeff

end WeightTwoCusps
