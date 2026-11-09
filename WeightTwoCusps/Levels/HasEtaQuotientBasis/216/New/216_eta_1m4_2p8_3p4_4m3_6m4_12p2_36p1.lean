module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-4) η(12z)^2 η(36z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-4) η(12z)^2 η(36z)` at level 216. -/
abbrev cuspForm_216_eta_1m4_2p8_3p4_4m3_6m4_12p2_36p1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -4, 11 => 2, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m4_2p8_3p4_4m3_6m4_12p2_36p1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m4_2p8_3p4_4m3_6m4_12p2_36p1 =
    [0, 0, 1, 4, 6, 4, 0, 0, 6, 8, 6, 4, 0, 0, -1, 4, 6, -4, 0, 0,
     0, 0, -6, 4, 0, 0, 5, -8, -6, 0, 0, 0, -12, -8, 0, -12, 0, 0, -7, -8,
     -18, 0, 0, 0, 0, -16, -12, -12, 0, 0, -5, -4, -24, -8, 0, 0, -6, -16, 12, 4,
     0, 0, -4, 0, 6, 4, 0, 0, 0, 16, -6, 8, 0, 0, 11, -4, 12, -12, 0, 0,
     0, 8, -12, 8, 0, 0, 8, -12, 18, 12, 0, 0, 0, 32, 12, -4, 0, 0, -6, 32] := by
  eta_coeff

end WeightTwoCusps
