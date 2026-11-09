module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(2z) η(5z) η(10z)^(-1) η(25z)^(-1) η(35z)^(-1) η(50z)^2 η(70z)^3 η(175z) η(350z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z) η(5z) η(10z)^(-1) η(25z)^(-1) η(35z)^(-1) η(50z)^2 η(70z)^3 η(175z) η(350z)^(-1)` at level 350. -/
abbrev cuspForm_350_eta_2p1_5p1_10m1_25m1_35m1_50p2_70p3_175p1_350m1 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 1 => 1, 4 => 1, 9 => -1, 24 => -1, 34 => -1, 49 => 2, 69 => 3, 174 => 1, 349 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_2p1_5p1_10m1_25m1_35m1_50p2_70p3_175p1_350m1_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_2p1_5p1_10m1_25m1_35m1_50p2_70p3_175p1_350m1 =
    [0, 0, 0, 1, 0, -1, 0, -1, -1, 0, 1, 0, 1, 1, 0, 0, 0, 1, -2, 0,
     1, 0, 0, 1, 0, -1, 0, -2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 1, 0, 0, -1, 0,
     -1, 0, -2, 2, 0, -2, 0, -1, -1, 0, 0, 0, 2, 0, 0, 2, 0, 3, 2, 0,
     -1, 0, -2, -1, 0, -1, 0, -4, 3, 0, 0, 0, 1, -3, 0, 1, 0, 3, 2, 0] := by
  eta_coeff

end WeightTwoCusps
