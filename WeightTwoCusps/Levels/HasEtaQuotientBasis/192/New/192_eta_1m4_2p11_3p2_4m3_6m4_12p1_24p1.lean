module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-4) η(2z)^11 η(3z)^2 η(4z)^(-3) η(6z)^(-4) η(12z) η(24z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^11 η(3z)^2 η(4z)^(-3) η(6z)^(-4) η(12z) η(24z)` at level 192. -/
abbrev cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -4, 1 => 11, 2 => 2, 3 => -3, 5 => -4, 11 => 1, 23 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1 =
    [0, 1, 4, 3, -6, -10, -6, 0, 12, 9, -8, -12, -6, 18, 24, 6, 0, -22, -12, 12,
     12, 12, -24, -24, -12, -1, 24, 3, 0, -26, -12, 24, 0, 12, 8, 0, -6, 2, 24, 6,
     -24, -14, 0, -12, 24, 6, 0, 0, 0, 41, -4, 6, 12, -2, -6, -24, 0, -12, -40, -12,
     12, -38, -24, 0, 0, 12, 0, 12, -12, 0, 48, 24, 12, -6, -8, -3, -24, 48, 12, -24,
     0, -15, 40, 12, 0, 28, -24, -18, 48, 10, 24, 0, -48, -12, -48, 24, 0, -78, -28, -12] := by
  eta_coeff

end WeightTwoCusps
