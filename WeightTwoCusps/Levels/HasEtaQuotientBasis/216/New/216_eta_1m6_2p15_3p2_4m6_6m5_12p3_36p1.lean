module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-5) η(12z)^3 η(36z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-5) η(12z)^3 η(36z)` at level 216. -/
abbrev cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -5, 11 => 3, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1 =
    [0, 0, 1, 6, 12, 6, -6, 0, 12, 12, 12, 6, 0, 0, -7, 6, 12, -6, 0, 0,
     0, 0, -12, 6, 0, 0, 17, -12, -12, 0, 0, 0, -24, -12, 0, -18, 0, 0, -13, -12,
     -36, 0, 24, 0, 0, -24, -24, -18, 0, 0, -5, -6, -48, -12, 0, 0, -12, -24, 24, 6,
     0, 0, -4, 0, 12, 6, 0, 0, 0, 24, -12, 12, 0, 0, 23, -6, 24, -18, -12, 0,
     0, 12, -24, 12, 0, 0, 8, -18, 36, 18, 0, 0, 0, 48, 24, -6, 0, 0, -30, 48] := by
  eta_coeff

end WeightTwoCusps
