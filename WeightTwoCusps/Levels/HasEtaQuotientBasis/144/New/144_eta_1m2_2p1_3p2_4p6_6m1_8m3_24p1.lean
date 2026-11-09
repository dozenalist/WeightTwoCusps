module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-2) η(2z) η(3z)^2 η(4z)^6 η(6z)^(-1) η(8z)^(-3) η(24z)`; see
[the local level table](../../TABLE.md#level-144).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^2 η(4z)^6 η(6z)^(-1) η(8z)^(-3) η(24z)` at level 144. -/
abbrev cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1 : gamma0CuspForms 144 :=
  etaQuotientCuspForm 144 sparse![144; 0 => -2, 1 => 1, 2 => 2, 3 => 6, 5 => -1, 7 => -3, 23 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1 =
    [0, 1, 2, 4, 6, 4, 4, 0, 0, 4, 2, 8, 0, -2, 0, -8, 0, -4, -4, 4,
     0, 0, -4, -16, 0, -1, -4, 4, -24, -12, -8, -8, 0, -16, -2, 0, 0, 6, -8, -8,
     0, 12, 0, -4, 0, -8, 8, 0, 0, -7, -2, 8, 12, 4, 4, 8, 0, 16, -6, 8,
     0, -2, 16, 0, 0, -8, 16, 4, 0, 32, 0, 16, 0, 10, 12, -4, 48, 0, -8, 8,
     0, 4, 6, -8, 0, -4, 8, 24, 0, 12, 8, 0, 0, -32, 0, 16, 0, 2, -14, -16] := by
  eta_coeff

end WeightTwoCusps
