module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(2z)^(-1) η(4z)^2 η(8z) η(26z) η(52z)^(-1) η(156z) η(312z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(8z) η(26z) η(52z)^(-1) η(156z) η(312z)` at level 312. -/
abbrev cuspForm_312_eta_2m1_4p2_8p1_26p1_52m1_156p1_312p1 : gamma0CuspForms 312 :=
  etaQuotientCuspForm 312 sparse![312; 1 => -1, 3 => 2, 7 => 1, 25 => 1, 51 => -1, 155 => 1, 311 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_312_eta_2m1_4p2_8p1_26p1_52m1_156p1_312p1_first_coeffs :
    first_coeffs 100 cuspForm_312_eta_2m1_4p2_8p1_26p1_52m1_156p1_312p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, 1, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 0,
     0, -1, 0, 0, 0, -1, 0, -3, 0, 1, 0, -1, 0, 1, 0, 0, 0, -2, 0, 2,
     0, 3, 0, 1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 1,
     0, 2, 0, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 2, 0, -2, 0, -2] := by
  eta_coeff

end WeightTwoCusps
