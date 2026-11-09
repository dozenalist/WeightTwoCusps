module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z)^3 η(5z)^(-1) η(6z)^(-1) η(7z)^2 η(10z)^3 η(14z)^(-1) η(30z)^(-1) η(105z)^(-1) η(210z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(5z)^(-1) η(6z)^(-1) η(7z)^2 η(10z)^3 η(14z)^(-1) η(30z)^(-1) η(105z)^(-1) η(210z)^2` at level 210. -/
abbrev cuspForm_210_eta_1m1_3p3_5m1_6m1_7p2_10p3_14m1_30m1_105m1_210p2 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 3, 4 => -1, 5 => -1, 6 => 2, 9 => 3, 13 => -1, 29 => -1, 104 => -1, 209 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_3p3_5m1_6m1_7p2_10p3_14m1_30m1_105m1_210p2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_3p3_5m1_6m1_7p2_10p3_14m1_30m1_105m1_210p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 2, 4,
     1, 1, 0, 4, -1, 1, -3, 1, -1, -1, 1, 2, -2, -1, -2, 1, -2, -7, -2, -4,
     -5, -5, -3, 0, -2, -3, 4, 6, -1, 0, -3, 1, -1, -4, -2, -2, -4, 1, -1, -5,
     0, -2, 6, -3, -2, -6, 2, -8, 0, -1, 1, 3, 0, -2, 7, 0, 6, 4, -2, 14,
     4, 2, 1, -4, 3, 3, 2, 6, 0, -7, 4, 2, 2, -3, 4, 5, 4, -12, 0, 2] := by
  eta_coeff

end WeightTwoCusps
