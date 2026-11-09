module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z)^4 η(6z)^(-1) η(10z) η(14z) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)^4 η(210z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^4 η(6z)^(-1) η(10z) η(14z) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)^4 η(210z)^(-1)` at level 210. -/
abbrev cuspForm_210_eta_1m1_3p4_6m1_10p1_14p1_15m1_21m1_35m1_105p4_210m1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 4, 5 => -1, 9 => 1, 13 => 1, 14 => -1, 20 => -1, 34 => -1, 104 => 4, 209 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_3p4_6m1_10p1_14p1_15m1_21m1_35m1_105p4_210m1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_3p4_6m1_10p1_14p1_15m1_21m1_35m1_105p4_210m1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 2, -1, 1, -1, 2, -2, 0, -1, 0, -4, -1,
     -2, 1, -4, 1, 3, -1, -3, -3, 5, 1, 1, -1, 6, -4, 1, -3, 4, -2, -1, 1,
     4, -3, 0, 0, 4, 6, 1, 3, -2, -2, 1, -1, -3, 3, 0, 3, -3, -5, 4, -4,
     -1, 2, 1, -1, -8, -4, 8, -2, -3, 1, 1, 2, -3, -3, 8, 1, 7, 5, -1, 3,
     -3, -3, 1, -2, -4, -4, -10, 8, -4, -3, -5, 6, 5, -1, -12, 3, -2, 2, 4, 3] := by
  eta_coeff

end WeightTwoCusps
