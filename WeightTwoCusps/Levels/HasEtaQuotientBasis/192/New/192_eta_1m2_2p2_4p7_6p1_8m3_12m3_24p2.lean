module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-2) η(2z)^2 η(4z)^7 η(6z) η(8z)^(-3) η(12z)^(-3) η(24z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(4z)^7 η(6z) η(8z)^(-3) η(12z)^(-3) η(24z)^2` at level 192. -/
abbrev cuspForm_192_eta_1m2_2p2_4p7_6p1_8m3_12m3_24p2 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -2, 1 => 2, 3 => 7, 5 => 1, 7 => -3, 11 => -3, 23 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m2_2p2_4p7_6p1_8m3_12m3_24p2_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m2_2p2_4p7_6p1_8m3_12m3_24p2 =
    [0, 1, 2, 3, 6, 2, 0, 0, -12, -3, -4, -12, 6, -6, 0, 6, 0, 2, -6, 12,
     -12, 0, 0, -24, 12, -1, 12, 3, 0, 10, 0, 24, 0, 0, 4, 0, 6, 2, 0, 6,
     24, 10, 0, -12, -24, -6, 0, 0, 0, -7, -2, 6, -12, -14, 0, -24, 0, 0, -20, -12,
     -12, 10, 0, 0, 0, -12, 0, 12, 12, 0, 0, 24, -12, -6, -4, -3, 24, 0, 0, -24,
     0, 9, 20, 12, 0, 4, 0, -18, -48, 10, 12, 0, 48, 0, 0, 24, 0, 18, -14, -12] := by
  eta_coeff

end WeightTwoCusps
