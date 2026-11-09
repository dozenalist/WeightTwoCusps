module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-3) η(96z)^6 η(192z)^(-2)`; see
[the local level table](../../TABLE.md#level-192).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-3) η(96z)^6 η(192z)^(-2)` at level 192. -/
abbrev cuspForm_192_eta_2m2_4p5_8m2_16p2_24p1_32m1_48m3_96p6_192m2 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 1 => -2, 3 => 5, 7 => -2, 15 => 2, 23 => 1, 31 => -1, 47 => -3, 95 => 6, 191 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_2m2_4p5_8m2_16p2_24p1_32m1_48m3_96p6_192m2_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_2m2_4p5_8m2_16p2_24p1_32m1_48m3_96p6_192m2 =
    [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2,
     0, -2, 0, 0, 0, 0, 0, -5, 0, -2, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0,
     0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 6, 0, 0, 0, 0, 0, 2,
     0, 4, 0, 0, 0, 0, 0, -2, 0, -4, 0, 0, 0, 0, 0, -1, 0, -8, 0, 0,
     0, 0, 0, -2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
