module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-4) η(9z)^(-2) η(12z) η(18z) η(36z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-4) η(9z)^(-2) η(12z) η(18z) η(36z)` at level 216. -/
abbrev cuspForm_216_eta_1m3_2p3_3p7_6m4_9m2_12p1_18p1_36p1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -3, 1 => 3, 2 => 7, 5 => -4, 8 => -2, 11 => 1, 17 => 1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p3_3p7_6m4_9m2_12p1_18p1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p3_3p7_6m4_9m2_12p1_18p1_36p1 =
    [0, 0, 1, 3, 6, 6, 3, 0, 0, 6, 6, 6, 0, 0, 5, 3, 6, -6, 0, 0,
     0, 0, -6, 6, 0, 0, -7, -6, -6, 0, 0, 0, 0, -6, 0, -18, 0, 0, -1, -6,
     -18, 0, -12, 0, 0, -12, -12, -18, 0, 0, -5, -3, -24, -12, 0, 0, 0, -12, 12, 6,
     0, 0, -4, 0, 6, 6, 0, 0, 0, 12, -6, 12, 0, 0, -1, -3, 12, -18, 6, 0,
     0, 6, -12, 12, 0, 0, 8, -9, 18, 18, 0, 0, 0, 24, 12, -6, 0, 0, 18, 24] := by
  eta_coeff

end WeightTwoCusps
