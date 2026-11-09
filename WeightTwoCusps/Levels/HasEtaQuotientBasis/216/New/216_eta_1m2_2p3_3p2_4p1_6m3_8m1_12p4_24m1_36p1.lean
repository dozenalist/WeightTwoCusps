module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-3) η(8z)^(-1) η(12z)^4 η(24z)^(-1) η(36z)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-3) η(8z)^(-1) η(12z)^4 η(24z)^(-1) η(36z)` at level 216. -/
abbrev cuspForm_216_eta_1m2_2p3_3p2_4p1_6m3_8m1_12p4_24m1_36p1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -3, 7 => -1, 11 => 4, 23 => -1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m2_2p3_3p2_4p1_6m3_8m1_12p4_24m1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m2_2p3_3p2_4p1_6m3_8m1_12p4_24m1_36p1 =
    [0, 0, 1, 2, 2, 2, 0, 0, 2, 4, 6, 2, 0, 0, -1, 2, 2, -2, 0, 0,
     0, 0, -6, 2, 0, 0, 5, -4, -2, 0, 0, 0, -4, -4, 0, -6, 0, 0, -7, -4,
     -6, 0, 0, 0, 0, -8, -12, -6, 0, 0, -5, -2, -8, -4, 0, 0, -2, -8, 12, 2,
     0, 0, -4, 0, 2, 2, 0, 0, 0, 8, -6, 4, 0, 0, 11, -2, 4, -6, 0, 0,
     0, 4, -12, 4, 0, 0, 8, -6, 6, 6, 0, 0, 0, 16, 12, -2, 0, 0, -6, 16] := by
  eta_coeff

end WeightTwoCusps
