module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(5z)^(-1) η(10z)^3 η(14z) η(25z) η(35z) η(50z)^(-1) η(70z)^(-1) η(175z)^(-1) η(350z)^2`; see
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

/-- The cuspidal eta quotient `η(5z)^(-1) η(10z)^3 η(14z) η(25z) η(35z) η(50z)^(-1) η(70z)^(-1) η(175z)^(-1) η(350z)^2` at level 350. -/
abbrev cuspForm_350_eta_5m1_10p3_14p1_25p1_35p1_50m1_70m1_175m1_350p2 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 4 => -1, 9 => 3, 13 => 1, 24 => 1, 34 => 1, 49 => -1, 69 => -1, 174 => -1, 349 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_5m1_10p3_14p1_25p1_35p1_50m1_70m1_175m1_350p2_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_5m1_10p3_14p1_25p1_35p1_50m1_70m1_175m1_350p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0,
     -1, -1, 0, 0, 0, 1, -3, 0, 0, -1, 0, 0, 0, 0, -1, 1, -1, 0, 0, 1,
     3, -2, 0, 0, 0, 0, 2, 0, 0, 1, 1, 3, 0, 0, 3, 2, 1, 0, 0, 0,
     -2, 3, 0, 0, 1, -3, 2, 0, 0, 2, -1, 1, 0, 0, -2, -3, 2, 0, 0, -3] := by
  eta_coeff

end WeightTwoCusps
