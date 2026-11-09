module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(4z)^(-2) η(8z)^5 η(14z)^2 η(28z)^(-1) η(32z)^(-1) η(56z) η(112z)^(-1) η(224z)`; see
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

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^5 η(14z)^2 η(28z)^(-1) η(32z)^(-1) η(56z) η(112z)^(-1) η(224z)` at level 224. -/
abbrev cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1 : gamma0CuspForms 224 :=
  etaQuotientCuspForm 224 sparse![224; 3 => -2, 7 => 5, 13 => 2, 27 => -1, 31 => -1, 55 => 1, 111 => -1, 223 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_4m2_8p5_14p2_28m1_32m1_56p1_112m1_224p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
     0, -2, 0, 0, 0, -4, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4,
     0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, -4, 0, -4,
     0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 8, 0, 4, 0, 2, 0, 0,
     0, 4, 0, -4, 0, -8, 0, 0, 0, -8, 0, 0, 0, 0, 0, -4, 0, -8, 0, 2] := by
  eta_coeff

end WeightTwoCusps
