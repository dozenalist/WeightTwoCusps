module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-1) η(8z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-1) η(8z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)` at level 288. -/
abbrev cuspForm_288_eta_1m3_2p6_3p1_4m1_8m1_16p2_24p1_32m1_48m1_96p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 6, 2 => 1, 3 => -1, 7 => -1, 15 => 2, 23 => 1, 31 => -1, 47 => -1, 95 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m3_2p6_3p1_4m1_8m1_16p2_24p1_32m1_48m1_96p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m3_2p6_3p1_4m1_8m1_16p2_24p1_32m1_48m1_96p1 =
    [0, 0, 0, 1, 3, 3, 3, 4, 3, 4, 3, 3, 6, 4, 9, 6, 0, 6, 3, 6,
     3, 0, 6, -2, 0, 0, -3, 1, 0, 1, -6, -8, 0, -4, -3, -4, -6, -4, -15, -2,
     0, -10, 0, -6, -6, -8, -12, 4, 0, 0, 3, -14, -6, -7, 3, -4, -12, 4, -9, -1,
     -12, -4, 3, -8, 0, -14, -12, -2, -3, 8, 0, -6, 0, -8, 12, -1, -12, 0, -6, 0,
     0, -8, 9, 5, 0, 0, -21, -2, 0, 8, -6, -8, 12, -8, 0, -2, 0, 8, -12, 12] := by
  eta_coeff

end WeightTwoCusps
