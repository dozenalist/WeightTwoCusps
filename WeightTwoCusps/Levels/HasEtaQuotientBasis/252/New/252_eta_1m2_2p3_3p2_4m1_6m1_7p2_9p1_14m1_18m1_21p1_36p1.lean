module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z)^(-1) η(6z)^(-1) η(7z)^2 η(9z) η(14z)^(-1) η(18z)^(-1) η(21z) η(36z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z)^(-1) η(6z)^(-1) η(7z)^2 η(9z) η(14z)^(-1) η(18z)^(-1) η(21z) η(36z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p3_3p2_4m1_6m1_7p2_9p1_14m1_18m1_21p1_36p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 5 => -1, 6 => 2, 8 => 1, 13 => -1, 17 => -1, 20 => 1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p3_3p2_4m1_6m1_7p2_9p1_14m1_18m1_21p1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p3_3p2_4m1_6m1_7p2_9p1_14m1_18m1_21p1_36p1 =
    [0, 0, 1, 2, 2, 2, 2, 4, 4, 2, 2, 1, 2, 2, 0, 2, 0, 0, 4, 2,
     4, 0, 0, 5, -2, -2, -2, -2, 0, -5, -2, 0, -3, 0, -4, 0, -2, -2, 2, -6,
     -2, -6, 0, 2, -11, -4, -2, -6, -2, -16, -9, -4, -6, 5, -10, -4, -1, -2, 4, -2,
     -6, -2, -2, 2, -4, -8, 0, -4, 6, -4, 0, 7, 0, -4, -4, 2, 6, 1, -2, -2,
     -10, 4, -4, 0, -4, 0, 8, 0, 2, -6, 0, 8, 5, 4, 4, -8, 10, 8, 1, -4] := by
  eta_coeff

end WeightTwoCusps
