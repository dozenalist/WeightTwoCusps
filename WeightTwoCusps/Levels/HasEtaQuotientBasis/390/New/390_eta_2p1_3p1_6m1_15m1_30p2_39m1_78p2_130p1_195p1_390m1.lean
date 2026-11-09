module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(2z) η(3z) η(6z)^(-1) η(15z)^(-1) η(30z)^2 η(39z)^(-1) η(78z)^2 η(130z) η(195z) η(390z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z) η(3z) η(6z)^(-1) η(15z)^(-1) η(30z)^2 η(39z)^(-1) η(78z)^2 η(130z) η(195z) η(390z)^(-1)` at level 390. -/
abbrev cuspForm_390_eta_2p1_3p1_6m1_15m1_30p2_39m1_78p2_130p1_195p1_390m1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 1 => 1, 2 => 1, 5 => -1, 14 => -1, 29 => 2, 38 => -1, 77 => 2, 129 => 1, 194 => 1, 389 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_2p1_3p1_6m1_15m1_30p2_39m1_78p2_130p1_195p1_390m1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_2p1_3p1_6m1_15m1_30p2_39m1_78p2_130p1_195p1_390m1 =
    [0, 0, 0, 0, 1, 0, -1, -1, -1, 1, 0, 1, 0, -1, 1, 1, 1, 0, 0, 0,
     -1, -1, 0, -1, 0, -1, 1, 0, 0, 1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0,
     1, 0, -1, 1, -1, -1, -1, -1, 2, 0, 2, -1, 0, 1, 1, 1, 0, 0, -1, -1,
     0, 0, 0, 1, -2, 0, 0, 0, 1, -1, -1, -1, 1, 0, -1, -2, 1, 0, 0, 1,
     0, -1, -1, 0, 1, 1, 1, 2, 1, 0, -1, 2, 0, 0, -1, 0, 0, -1, 1, 0] := by
  eta_coeff

end WeightTwoCusps
