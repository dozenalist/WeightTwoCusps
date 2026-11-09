module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(9z)^(-1) η(12z) η(14z)^(-1) η(18z)^2 η(21z)^2 η(28z) η(36z)^(-1) η(63z)^(-1) η(84z)^(-1) η(252z)^2`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(9z)^(-1) η(12z) η(14z)^(-1) η(18z)^2 η(21z)^2 η(28z) η(36z)^(-1) η(63z)^(-1) η(84z)^(-1) η(252z)^2` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_9m1_12p1_14m1_18p2_21p2_28p1_36m1_63m1_84m1_252p2 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 8 => -1, 11 => 1, 13 => -1, 17 => 2, 20 => 2, 27 => 1, 35 => -1, 62 => -1, 83 => -1, 251 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_9m1_12p1_14m1_18p2_21p2_28p1_36m1_63m1_84m1_252p2_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_9m1_12p1_14m1_18p2_21p2_28p1_36m1_63m1_84m1_252p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3,
     1, -1, 0, 3, 2, 2, 1, 0, 2, 0, 2, 1, 3, 6, 0, -1, -3, 1, -1, -4,
     -4, -5, 2, -3, -2, -2, -2, 2, -4, -5, -3, -4, 0, -2, -12, -4, -1, 4, 4, -3,
     -2, -2, 0, -1, 2, -7, -4, -2, -6, 2, -2, 0, 5, -8, -5, 4, -4, 4, -2, -10,
     1, 0, 0, 7, -2, 4, 3, -4, 8, 1, 2, 6, 5, -4, 8, 5, 2, 18, 0, 4] := by
  eta_coeff

end WeightTwoCusps
