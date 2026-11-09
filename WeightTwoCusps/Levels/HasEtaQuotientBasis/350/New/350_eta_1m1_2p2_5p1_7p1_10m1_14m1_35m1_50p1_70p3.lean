module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(z)^(-1) η(2z)^2 η(5z) η(7z) η(10z)^(-1) η(14z)^(-1) η(35z)^(-1) η(50z) η(70z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(5z) η(7z) η(10z)^(-1) η(14z)^(-1) η(35z)^(-1) η(50z) η(70z)^3` at level 350. -/
abbrev cuspForm_350_eta_1m1_2p2_5p1_7p1_10m1_14m1_35m1_50p1_70p3 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 0 => -1, 1 => 2, 4 => 1, 6 => 1, 9 => -1, 13 => -1, 34 => -1, 49 => 1, 69 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_1m1_2p2_5p1_7p1_10m1_14m1_35m1_50p1_70p3_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_1m1_2p2_5p1_7p1_10m1_14m1_35m1_50p1_70p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, 0, -1, -2, 0, 0,
     -1, 1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 2, -1, -1, 0, 0, 0, 2, 0,
     0, 3, 0, 0, -1, 0, 0, 0, 0, 2, 1, 0, 0, -2, 0, 0, -1, -2, 0, -1,
     -1, 0, -1, 0, 1, 2, 1, 2, 1, 1, 0, -1, 0, -2, 0, 1, 1, 0, 2, -1,
     -1, 0, -3, 1, 1, -1, -1, 2, 0, 2, 0, -4, 2, 0, 1, 1, 0, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
