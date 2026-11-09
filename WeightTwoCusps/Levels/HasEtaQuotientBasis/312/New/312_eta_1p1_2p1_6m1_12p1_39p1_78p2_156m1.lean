module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(z) η(2z) η(6z)^(-1) η(12z) η(39z) η(78z)^2 η(156z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(6z)^(-1) η(12z) η(39z) η(78z)^2 η(156z)^(-1)` at level 312. -/
abbrev cuspForm_312_eta_1p1_2p1_6m1_12p1_39p1_78p2_156m1 : gamma0CuspForms 312 :=
  etaQuotientCuspForm 312 sparse![312; 0 => 1, 1 => 1, 5 => -1, 11 => 1, 38 => 1, 77 => 2, 155 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_312_eta_1p1_2p1_6m1_12p1_39p1_78p2_156m1_first_coeffs :
    first_coeffs 100 cuspForm_312_eta_1p1_2p1_6m1_12p1_39p1_78p2_156m1 =
    [0, 0, 1, -1, -2, 1, 0, 2, 2, -1, -2, -1, 1, 0, 0, -1, 0, -2, 1, 2,
     1, 0, -2, 0, 1, 4, 0, 0, -2, -2, 1, 0, -3, -1, 0, -2, 1, 2, 2, 0,
     -2, -1, 3, 4, 1, -1, -2, -5, 1, 4, 1, -1, 0, -2, 2, 0, 2, -2, -6, 1,
     1, 4, 0, -2, -6, -1, 0, 4, 2, -2, -2, 3, 2, 2, 4, -2, -2, -2, 0, 4,
     1, 1, 2, -5, 2, -6, -4, 2, 2, 1, -3, 0, 4, 0, -2, 6, -2, -2, -3, -3] := by
  eta_coeff

end WeightTwoCusps
