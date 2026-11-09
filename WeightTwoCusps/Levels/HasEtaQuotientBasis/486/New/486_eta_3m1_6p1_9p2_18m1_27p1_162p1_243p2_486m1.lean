module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(3z)^(-1) η(6z) η(9z)^2 η(18z)^(-1) η(27z) η(162z) η(243z)^2 η(486z)^(-1)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(9z)^2 η(18z)^(-1) η(27z) η(162z) η(243z)^2 η(486z)^(-1)` at level 486. -/
abbrev cuspForm_486_eta_3m1_6p1_9p2_18m1_27p1_162p1_243p2_486m1 : gamma0CuspForms 486 :=
  etaQuotientCuspForm 486 sparse![486; 2 => -1, 5 => 1, 8 => 2, 17 => -1, 26 => 1, 161 => 1, 242 => 2, 485 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_486_eta_3m1_6p1_9p2_18m1_27p1_162p1_243p2_486m1_first_coeffs :
    first_coeffs 100 cuspForm_486_eta_3m1_6p1_9p2_18m1_27p1_162p1_243p2_486m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0,
     0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0,
     0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0,
     -1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
