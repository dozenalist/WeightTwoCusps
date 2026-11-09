module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(10z) η(18z)^2 η(45z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(10z) η(18z)^2 η(45z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p5_6m3_9m2_10p1_18p2_45p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 9 => 1, 17 => 2, 44 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p5_6m3_9m2_10p1_18p2_45p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p5_6m3_9m2_10p1_18p2_45p1 =
    [0, 0, 0, 1, 2, 3, 1, -1, -1, 0, 3, 0, 1, -2, -1, 0, -1, 3, -2, 1,
     -5, -2, -1, 0, -1, -9, -2, -2, 5, 0, -1, 2, -1, 1, -4, -3, 0, 0, 1, 0,
     2, 3, -1, -2, -1, 2, 0, -3, -3, -5, 0, -2, 0, 3, 4, 7, 2, 0, 4, 0,
     0, 1, -1, 4, 0, 12, 6, 8, -1, 0, 1, -3, 6, -5, 3, 1, -3, -3, -1, 5,
     9, 0, 4, -3, -2, 1, 1, 2, -3, 6, -4, 4, 3, 4, 2, -18, 1, -3, 1, -4] := by
  eta_coeff

end WeightTwoCusps
