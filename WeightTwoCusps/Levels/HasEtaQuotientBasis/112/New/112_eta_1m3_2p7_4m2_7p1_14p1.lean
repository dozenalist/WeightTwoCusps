module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 112

The eta expression is `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(7z) η(14z)`; see
[the local level table](../../TABLE.md#level-112).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(7z) η(14z)` at level 112. -/
abbrev cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1 : gamma0CuspForms 112 :=
  etaQuotientCuspForm 112 sparse![112; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1 =
    [0, 1, 3, 2, 1, 4, 2, 1, 3, -3, 0, 4, -2, 0, -1, -4, -3, -2, -5, -10,
     0, -2, -8, 4, -6, -9, 4, -4, 1, 2, -8, -4, 3, 0, -14, 0, 1, 2, 14, -4,
     0, 6, 2, 4, 0, -4, 8, 12, 6, 1, 9, 4, -4, 14, -4, 8, 3, 0, 14, 6,
     0, -4, 20, -3, -3, 4, 0, 0, 6, -8, -8, 8, 3, 18, -10, 6, 2, 4, 0, -24,
     0, 9, 2, -2, -2, -16, 0, -4, 0, -14, -16, 4, 0, 0, -20, -12, -6, -10, 3, -12] := by
  eta_coeff

end WeightTwoCusps
