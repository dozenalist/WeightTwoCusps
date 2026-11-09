module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-2) η(7z)^2 η(12z) η(14z)^(-2) η(21z)^(-2) η(28z) η(42z)^5 η(84z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-2) η(7z)^2 η(12z) η(14z)^(-2) η(21z)^(-2) η(28z) η(42z)^5 η(84z)^(-2)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p3_3p2_6m2_7p2_12p1_14m2_21m2_28p1_42p5_84m2 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 3, 2 => 2, 5 => -2, 6 => 2, 11 => 1, 13 => -2, 20 => -2, 27 => 1, 41 => 5, 83 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p3_3p2_6m2_7p2_12p1_14m2_21m2_28p1_42p5_84m2_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p3_3p2_6m2_7p2_12p1_14m2_21m2_28p1_42p5_84m2 =
    [0, 1, 2, 2, 2, 1, 2, 3, 2, 1, -2, -1, 2, 1, 0, -2, -2, 3, 2, 1,
     0, -1, 4, 3, 2, 1, 0, 2, 2, -1, -2, -2, 0, 0, 0, -1, -4, 1, 0, 0,
     -2, -5, 0, -1, -6, -2, -6, -2, -2, -11, -6, -6, -2, -1, -10, -9, 0, 0, 4, -6,
     -6, -4, -4, 0, -4, -6, -8, -4, 0, 0, -4, 1, 2, 1, -4, -2, -2, 4, 6, -2,
     -4, 1, 8, 8, -4, -2, 4, 0, 4, 3, 4, 7, 6, 4, 12, 4, 6, 15, 2, 2] := by
  eta_coeff

end WeightTwoCusps
