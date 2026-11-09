module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(z)^(-1) η(4z)^5 η(7z) η(8z)^(-2) η(14z)^(-1) η(28z) η(56z)^(-1) η(112z)^2`; see
[the local level table](../../TABLE.md#level-224).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(4z)^5 η(7z) η(8z)^(-2) η(14z)^(-1) η(28z) η(56z)^(-1) η(112z)^2` at level 224. -/
abbrev cuspForm_224_eta_1m1_4p5_7p1_8m2_14m1_28p1_56m1_112p2 : gamma0CuspForms 224 :=
  etaQuotientCuspForm 224 sparse![224; 0 => -1, 3 => 5, 6 => 1, 7 => -2, 13 => -1, 27 => 1, 55 => -1, 111 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_1m1_4p5_7p1_8m2_14m1_28p1_56m1_112p2_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_1m1_4p5_7p1_8m2_14m1_28p1_56m1_112p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 0, 2, 1, -1, 3, 0, -2, 2,
     0, -1, 2, -3, -2, 1, 2, 0, 0, 0, -2, 2, -3, -4, -4, -1, 0, -2, -4, -3,
     0, 2, 0, -3, 0, -2, 2, -4, -6, 0, -2, -2, 0, -2, 0, 6, 1, -5, 4, 0,
     0, 4, -4, 1, 3, -1, 0, 1, 0, 2, 0, 2, 1, 4, 0, -4, 0, -1, 2, 0,
     0, 7, 0, 2, 0, 2, 6, 2, 0, -6, -2, -1, 0, -6, 0, 1, 6, 2, 0, -1] := by
  eta_coeff

end WeightTwoCusps
