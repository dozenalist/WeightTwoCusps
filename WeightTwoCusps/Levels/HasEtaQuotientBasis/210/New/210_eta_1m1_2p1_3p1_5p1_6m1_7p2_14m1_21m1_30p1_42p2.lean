module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(6z)^(-1) η(7z)^2 η(14z)^(-1) η(21z)^(-1) η(30z) η(42z)^2`; see
[the local level table](../../TABLE.md#level-210).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(6z)^(-1) η(7z)^2 η(14z)^(-1) η(21z)^(-1) η(30z) η(42z)^2` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_3p1_5p1_6m1_7p2_14m1_21m1_30p1_42p2 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 5 => -1, 6 => 2, 13 => -1, 20 => -1, 29 => 1, 41 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_3p1_5p1_6m1_7p2_14m1_21m1_30p1_42p2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_3p1_5p1_6m1_7p2_14m1_21m1_30p1_42p2 =
    [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 0, 0, 1, 0, -1,
     -1, 1, 0, 1, -1, -2, 0, 0, 1, 1, 0, -1, 0, 0, 1, -1, -3, -5, -3, 0,
     1, 0, -1, -2, 0, 1, 1, -2, -4, -4, -2, -1, 2, -1, -1, 0, -1, 2, 1, -1,
     -2, -2, -1, 1, 1, 1, -2, 2, -1, 0, 0, 1, -1, -1, -1, 1, 3, 2, 5, 4,
     3, 1, 2, 2, 1, -2, 0, -1, 0, 2, -1, 1, -3, 2, -2, 2, 3, -1, 4, -1] := by
  eta_coeff

end WeightTwoCusps
