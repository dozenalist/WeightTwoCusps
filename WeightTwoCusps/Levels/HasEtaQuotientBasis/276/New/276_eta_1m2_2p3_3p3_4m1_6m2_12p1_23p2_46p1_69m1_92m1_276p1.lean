module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-2) η(12z) η(23z)^2 η(46z) η(69z)^(-1) η(92z)^(-1) η(276z)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(6z)^(-2) η(12z) η(23z)^2 η(46z) η(69z)^(-1) η(92z)^(-1) η(276z)` at level 276. -/
abbrev cuspForm_276_eta_1m2_2p3_3p3_4m1_6m2_12p1_23p2_46p1_69m1_92m1_276p1 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 22 => 2, 45 => 1, 68 => -1, 91 => -1, 275 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m2_2p3_3p3_4m1_6m2_12p1_23p2_46p1_69m1_92m1_276p1_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m2_2p3_3p3_4m1_6m2_12p1_23p2_46p1_69m1_92m1_276p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 2, 2, 2, 2, 1, 2,
     0, 2, 2, 0, 2, 2, 2, 1, 0, 2, 2, 2, 2, -4, -4, 0, 2, -2, -4, -3,
     -2, -2, -2, 2, -2, -2, 0, -2, -4, 0, 0, 2, -2, -4, -1, -10, -2, -2, -6, -4,
     -6, -2, -6, -8, 0, -4, -2, -6, -6, 0, -6, -2, -11, -6, -2, -6, -2, -8, -3, 8,
     8, 3, -2, 2, 8, 8, 8, 5, -2, -6, 2, 4, 0, 3, 8, 2, 3, -8, 2, 8] := by
  eta_coeff

end WeightTwoCusps
