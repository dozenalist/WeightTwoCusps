module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(3z)^(-2) η(6z)^5 η(8z) η(12z)^(-2) η(16z) η(48z)^(-1) η(96z)^2`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^5 η(8z) η(12z)^(-2) η(16z) η(48z)^(-1) η(96z)^2` at level 384. -/
abbrev cuspForm_384_eta_3m2_6p5_8p1_12m2_16p1_48m1_96p2 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 2 => -2, 5 => 5, 7 => 1, 11 => -2, 15 => 1, 47 => -1, 95 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_3m2_6p5_8p1_12m2_16p1_48m1_96p2_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_3m2_6p5_8p1_12m2_16p1_48m1_96p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, -1, 0, 0, -2, 2,
     0, 0, 0, -2, 0, 0, -4, -2, 0, 0, 0, 1, 0, 0, 4, -4, 0, 0, 0, 0,
     0, 0, -2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 6, 4,
     0, 0, 0, -3, 0, 0, -2, 4, 0, 0, 0, -6, 0, 0, 0, -2, 0, 0, 0, 1,
     0, 0, 4, -4, 0, 0, 0, 1, 0, 0, -2, -2, 0, 0, 0, 4, 0, 0, -8, 2] := by
  eta_coeff

end WeightTwoCusps
