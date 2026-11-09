module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(z) η(2z)^(-1) η(4z) η(7z)^(-1) η(8z)^(-1) η(16z)^2 η(28z)^5 η(56z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(4z) η(7z)^(-1) η(8z)^(-1) η(16z)^2 η(28z)^5 η(56z)^(-2)` at level 224. -/
abbrev cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2 : gamma0CuspForms 224 :=
  etaQuotientCuspForm 224 sparse![224; 0 => 1, 1 => -1, 3 => 1, 6 => -1, 7 => -1, 15 => 2, 27 => 5, 55 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_1p1_2m1_4p1_7m1_8m1_16p2_28p5_56m2 =
    [0, 0, 1, -1, 0, -1, 0, 0, 1, 1, 0, -1, 0, -1, 0, 1, 3, -2, -1, -1,
     0, 0, 2, 3, -2, -3, 0, -2, 0, 2, 2, 0, -3, 4, -2, 0, 0, 4, -4, -1,
     0, 0, 0, 1, 0, 1, -2, 2, -6, 0, 1, 4, 0, 2, 0, -2, 1, 3, 2, 1,
     0, -5, -4, 1, 3, -1, 0, -1, 0, -6, 2, 2, 1, 0, -2, 5, 0, 3, -2, -4,
     0, -1, 2, -1, 0, -4, -2, -4, 0, 6, -4, 2, 0, 2, 8, -1, 6, -4, 1, 3] := by
  eta_coeff

end WeightTwoCusps
