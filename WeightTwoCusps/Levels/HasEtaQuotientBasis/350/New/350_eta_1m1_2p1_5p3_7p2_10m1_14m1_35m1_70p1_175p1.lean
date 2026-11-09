module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(35z)^(-1) η(70z) η(175z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(35z)^(-1) η(70z) η(175z)` at level 350. -/
abbrev cuspForm_350_eta_1m1_2p1_5p3_7p2_10m1_14m1_35m1_70p1_175p1 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 0 => -1, 1 => 1, 4 => 3, 6 => 2, 9 => -1, 13 => -1, 34 => -1, 69 => 1, 174 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_1m1_2p1_5p3_7p2_10m1_14m1_35m1_70p1_175p1_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_1m1_2p1_5p3_7p2_10m1_14m1_35m1_70p1_175p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 0, 1, 0, -2, 0, -2,
     -3, 1, 0, -4, 2, -2, -4, 0, -2, -3, 2, -2, -4, 2, -2, 0, 0, 0, 0, 3,
     1, 0, 0, 0, 1, -1, 5, 6, 6, 2, 1, 3, 0, 0, -4, -1, 1, 4, -4, 2,
     0, -4, 0, -2, 1, 3, 4, -4, 4, 0, 1, -4, -4, 0, 3, 3, -2, -2, 0, 5,
     -1, 0, 4, 4, 0, -1, 3, -2, -4, -8, -3, 1, 8, -4, -2, 0, -6, -2, 0, -6] := by
  eta_coeff

end WeightTwoCusps
