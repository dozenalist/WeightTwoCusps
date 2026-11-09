module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(2z) η(4z) η(6z) η(12z)^(-1) η(156z)^2`; see
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

/-- The cuspidal eta quotient `η(2z) η(4z) η(6z) η(12z)^(-1) η(156z)^2` at level 312. -/
abbrev cuspForm_312_eta_2p1_4p1_6p1_12m1_156p2 : gamma0CuspForms 312 :=
  etaQuotientCuspForm 312 sparse![312; 1 => 1, 3 => 1, 5 => 1, 11 => -1, 155 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_312_eta_2p1_4p1_6p1_12m1_156p2_first_coeffs :
    first_coeffs 100 cuspForm_312_eta_2p1_4p1_6p1_12m1_156p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -2, 0, 0,
     0, 1, 0, 4, 0, 0, 0, 0, 0, -2, 0, -4, 0, 2, 0, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, 1, 0, 4, 0, 4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0,
     0, 0, 0, -3, 0, -4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -2, 0, 0,
     0, 2, 0, 0, 0, 4, 0, -2, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
