module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(4z) η(6z) η(8z) η(12z)^(-1) η(78z)^(-1) η(156z)^2 η(312z)`; see
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

/-- The cuspidal eta quotient `η(4z) η(6z) η(8z) η(12z)^(-1) η(78z)^(-1) η(156z)^2 η(312z)` at level 312. -/
abbrev cuspForm_312_eta_4p1_6p1_8p1_12m1_78m1_156p2_312p1 : gamma0CuspForms 312 :=
  etaQuotientCuspForm 312 sparse![312; 3 => 1, 5 => 1, 7 => 1, 11 => -1, 77 => -1, 155 => 2, 311 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_312_eta_4p1_6p1_8p1_12m1_78m1_156p2_312p1_first_coeffs :
    first_coeffs 100 cuspForm_312_eta_4p1_6p1_8p1_12m1_78m1_156p2_312p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0, -2, 0, 1, 0, 1, 0, 2, 0, 0,
     0, -2, 0, 2, 0, 1, 0, 2, 0, 0, 0, -1, 0, -3, 0, -2, 0, 1, 0, 0,
     0, 0, 0, 0, 0, -1, 0, -2, 0, 0, 0, 2, 0, 2, 0, -2, 0, 0, 0, 0,
     0, 1, 0, 2, 0, 2, 0, -1, 0, 0, 0, 0, 0, 1, 0, 3, 0, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
