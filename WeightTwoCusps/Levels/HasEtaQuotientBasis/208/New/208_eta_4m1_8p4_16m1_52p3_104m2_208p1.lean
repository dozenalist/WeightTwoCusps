module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 208

The eta expression is `η(4z)^(-1) η(8z)^4 η(16z)^(-1) η(52z)^3 η(104z)^(-2) η(208z)`; see
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

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z)^4 η(16z)^(-1) η(52z)^3 η(104z)^(-2) η(208z)` at level 208. -/
abbrev cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1 : gamma0CuspForms 208 :=
  etaQuotientCuspForm 208 sparse![208; 3 => -1, 7 => 4, 15 => -1, 51 => 3, 103 => -2, 207 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, -3,
     0, 0, 0, -1, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, -2, 0, 0, 0, 6,
     0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 0, 0, -3] := by
  eta_coeff

end WeightTwoCusps
