module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z) η(5z) η(10z)^(-1) η(15z)^(-1) η(30z)^2 η(39z)^(-1) η(78z)^2 η(130z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z) η(10z)^(-1) η(15z)^(-1) η(30z)^2 η(39z)^(-1) η(78z)^2 η(130z)` at level 390. -/
abbrev cuspForm_390_eta_1p1_5p1_10m1_15m1_30p2_39m1_78p2_130p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 0 => 1, 4 => 1, 9 => -1, 14 => -1, 29 => 2, 38 => -1, 77 => 2, 129 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_1p1_5p1_10m1_15m1_30p2_39m1_78p2_130p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_1p1_5p1_10m1_15m1_30p2_39m1_78p2_130p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 0, 1, 2,
     0, 0, -1, 0, -2, 0, 0, -1, 0, 1, 0, 0, 1, 0, 1, 0, 0, -1, 2, 0,
     0, 0, -1, -1, -1, 0, 0, -1, 0, 1, 0, 1, 1, -2, -1, 0, 0, 3, 2, 0,
     0, -1, 0, -2, -1, 0, -1, -1, 0, 1, 0, 1, 1, 1, 0, 0, -1, 3, 1, 0,
     0, -1, -2, -1, 0, 0, -1, 0, 0, -1, 0, 2, -1, -2, -1, 0, 2, 1, 0, 1] := by
  eta_coeff

end WeightTwoCusps
