module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(6z) η(7z) η(12z)^(-1) η(14z) η(28z)^(-1) η(42z)^(-1) η(84z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(6z) η(7z) η(12z)^(-1) η(14z) η(28z)^(-1) η(42z)^(-1) η(84z)^2` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p3_3p1_6p1_7p1_12m1_14p1_28m1_42m1_84p2 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 3, 2 => 1, 5 => 1, 6 => 1, 11 => -1, 13 => 1, 27 => -1, 41 => -1, 83 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p3_3p1_6p1_7p1_12m1_14p1_28m1_42m1_84p2_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p3_3p1_6p1_7p1_12m1_14p1_28m1_42m1_84p2 =
    [0, 0, 0, 0, 0, 1, 2, 2, 3, 3, 4, 4, 2, 3, 1, 3, 4, 1, 3, 1,
     2, 2, -3, -2, -4, -3, 0, -6, -1, -4, -3, 2, -4, 0, -8, -1, 0, -6, -2, -7,
     -2, 3, -1, 0, -5, -2, 4, -8, 0, -12, -2, 2, -4, 2, -4, 5, -2, 1, 1, -4,
     -5, 4, -2, 2, -3, 4, 4, 0, 4, -10, 5, -4, -3, -5, -4, -2, 6, -1, -3, -5,
     0, 6, -14, 0, -3, 2, 6, 2, 0, -5, -2, 4, 1, 2, -6, -6, 10, -3, 0, -8] := by
  eta_coeff

end WeightTwoCusps
