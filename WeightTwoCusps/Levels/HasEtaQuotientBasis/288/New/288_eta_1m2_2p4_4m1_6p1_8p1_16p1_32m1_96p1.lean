module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(6z) η(8z) η(16z) η(32z)^(-1) η(96z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(6z) η(8z) η(16z) η(32z)^(-1) η(96z)` at level 288. -/
abbrev cuspForm_288_eta_1m2_2p4_4m1_6p1_8p1_16p1_32m1_96p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 4, 3 => -1, 5 => 1, 7 => 1, 15 => 1, 31 => -1, 95 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m2_2p4_4m1_6p1_8p1_16p1_32m1_96p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m2_2p4_4m1_6p1_8p1_16p1_32m1_96p1 =
    [0, 0, 0, 0, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 3, 4, 0, 2, 3, 4,
     1, -2, 2, -2, 0, 0, -3, 0, 0, 0, -2, -6, 0, 2, -3, -2, -2, 0, -5, 0,
     0, -4, 0, -4, -2, -2, -4, 2, 0, -4, 3, -8, -2, -2, 1, 0, -12, -2, -9, 0,
     -4, -4, 1, -4, 0, -8, -12, 0, -1, 0, 0, -2, 0, 0, 12, 0, -4, -2, -2, 2,
     0, -4, 9, 2, 0, 2, -7, -4, 0, 6, -6, -4, 4, 2, 0, 0, 0, 8, -12, 8] := by
  eta_coeff

end WeightTwoCusps
