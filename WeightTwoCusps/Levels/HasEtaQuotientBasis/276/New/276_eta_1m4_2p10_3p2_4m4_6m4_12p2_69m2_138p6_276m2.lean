module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(69z)^(-2) η(138z)^6 η(276z)^(-2)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(69z)^(-2) η(138z)^6 η(276z)^(-2)` at level 276. -/
abbrev cuspForm_276_eta_1m4_2p10_3p2_4m4_6m4_12p2_69m2_138p6_276m2 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 68 => -2, 137 => 6, 275 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m4_2p10_3p2_4m4_6m4_12p2_69m2_138p6_276m2_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m4_2p10_3p2_4m4_6m4_12p2_69m2_138p6_276m2 =
    [0, 0, 0, 0, 0, 0, 1, 4, 4, -2, -4, 0, 3, 4, 0, -2, -4, -8, 1, 4,
     0, -2, -8, 0, 2, 0, 4, -4, -4, 0, 2, 4, 0, -2, -4, -8, 1, 8, 0, 0,
     -4, 0, 4, 4, 8, -2, 0, 0, 3, 4, 0, -2, -8, 0, 2, 4, 0, -4, 0, 0,
     0, 8, 12, -2, -4, 0, 2, 4, 0, 0, -4, -8, 4, 4, 0, 0, 4, 8, -1, -4,
     0, 6, 0, 0, -2, -4, -16, -4, 8, -8, -2, -16, 0, 2, -4, 8, -7, 0, 8, 2] := by
  eta_coeff

end WeightTwoCusps
