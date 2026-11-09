module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(5z) η(6z)^(-2) η(10z) η(15z)^(-1) η(45z)`; see
[the local level table](../../TABLE.md#level-270).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(5z) η(6z)^(-2) η(10z) η(15z)^(-1) η(45z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p5_5p1_6m2_10p1_15m1_45p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 5, 4 => 1, 5 => -2, 9 => 1, 14 => -1, 44 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p5_5p1_6m2_10p1_15m1_45p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p5_5p1_6m2_10p1_15m1_45p1 =
    [0, 0, 1, 2, 4, 3, 4, 3, 5, 4, 5, 6, 4, 1, -2, 2, 2, 3, 2, 6,
     2, 0, 0, 5, 0, 1, -2, 2, -8, -8, -2, -4, 2, -2, 6, -6, -4, -3, 3, -4,
     -2, 2, -6, -8, -6, -2, -4, -12, -2, -2, -13, -8, -14, -5, -8, -3, -4, -10, -8, -8,
     -2, -10, 3, -12, -10, -8, -4, 1, -6, 0, -5, -2, -6, 5, 2, 2, 6, -4, -2, -2,
     -1, 4, 2, 3, 0, -6, -8, 8, 6, 6, 8, -8, 8, 0, -6, 9, -4, 19, -7, -4] := by
  eta_coeff

end WeightTwoCusps
