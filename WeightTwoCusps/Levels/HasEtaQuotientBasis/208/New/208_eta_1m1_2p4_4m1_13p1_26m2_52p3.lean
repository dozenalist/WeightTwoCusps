module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 208

The eta expression is `η(z)^(-1) η(2z)^4 η(4z)^(-1) η(13z) η(26z)^(-2) η(52z)^3`; see
[the local level table](../../TABLE.md#level-208).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^4 η(4z)^(-1) η(13z) η(26z)^(-2) η(52z)^3` at level 208. -/
abbrev cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3 : gamma0CuspForms 208 :=
  etaQuotientCuspForm 208 sparse![208; 0 => -1, 1 => 4, 3 => -1, 12 => 1, 25 => -2, 51 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3 =
    [0, 0, 0, 0, 0, 1, 1, -2, -1, 0, -2, 1, 0, 0, 2, 1, 2, -2, -1, 1,
     3, 1, -2, 2, -3, 0, -1, -2, -1, -4, 2, 1, -1, -4, 1, 0, -2, 5, 0, 1,
     4, 4, 4, -2, -4, 0, 6, 2, 0, 6, -5, -2, -1, -6, -5, -8, 2, 2, -2, -5,
     1, 0, -4, 5, 2, 2, 2, 3, 6, 2, -5, -2, 6, -2, 6, 6, -6, 0, 0, -4,
     -5, -4, 2, 9, 1, -9, -5, 2, -10, 2, 2, 1, 6, 0, 10, -2, -3, 0, 11, -3] := by
  eta_coeff

end WeightTwoCusps
