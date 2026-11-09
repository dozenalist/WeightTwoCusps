module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(4z) η(10z) η(52z) η(130z)^(-1) η(260z)^2`; see
[the local level table](../../TABLE.md#level-260).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(10z) η(52z) η(130z)^(-1) η(260z)^2` at level 260. -/
abbrev cuspForm_260_eta_4p1_10p1_52p1_130m1_260p2 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 3 => 1, 9 => 1, 51 => 1, 129 => -1, 259 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_4p1_10p1_52p1_130m1_260p2_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_4p1_10p1_52p1_130m1_260p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 2, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0,
     0, 1, 0, 0, 0, -1, 0, 1, 0, 2, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
