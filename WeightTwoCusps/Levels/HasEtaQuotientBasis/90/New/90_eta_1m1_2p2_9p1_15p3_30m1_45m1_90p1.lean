module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 90

The eta expression is `η(z)^(-1) η(2z)^2 η(9z) η(15z)^3 η(30z)^(-1) η(45z)^(-1) η(90z)`; see
[the local level table](../../TABLE.md#level-90).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(9z) η(15z)^3 η(30z)^(-1) η(45z)^(-1) η(90z)` at level 90. -/
abbrev cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1 : gamma0CuspForms 90 :=
  etaQuotientCuspForm 90 sparse![90; 0 => -1, 1 => 2, 8 => 1, 14 => 3, 29 => -1, 44 => -1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1 =
    [0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -3, -3,
     0, -4, -2, 0, -3, 0, 0, 1, 0, 0, 3, 0, 0, 0, 1, 0, 3, 6, 0, 2,
     -1, 0, 4, 0, 0, -1, 0, 0, 7, 3, 0, 6, -2, 0, 1, 3, 0, -4, 2, 0,
     -3, 0, 0, -4, -1, 0, -8, -6, 0, 0, -1, 0, 1, -6, 0, 1, 1, 0, -6, 0,
     0, 1, 2, 0, -4, -3, 0, -6, 2, 0, -1, -3, 0, 8, 1, 0, -3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
