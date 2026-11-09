module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(5z)^(-2) η(8z) η(10z)^5 η(16z) η(20z)^(-2) η(40z)^2 η(80z)^(-1)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-2) η(8z) η(10z)^5 η(16z) η(20z)^(-2) η(40z)^2 η(80z)^(-1)` at level 320. -/
abbrev cuspForm_320_eta_5m2_8p1_10p5_16p1_20m2_40p2_80m1 : gamma0CuspForms 320 :=
  etaQuotientCuspForm 320 sparse![320; 4 => -2, 7 => 1, 9 => 5, 15 => 1, 19 => -2, 39 => 2, 79 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_320_eta_5m2_8p1_10p5_16p1_20m2_40p2_80m1_first_coeffs :
    first_coeffs 100 cuspForm_320_eta_5m2_8p1_10p5_16p1_20m2_40p2_80m1 =
    [0, 1, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0,
     0, 2, -4, 0, 0, 1, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, -4, 0, 0,
     0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0,
     0, 0, 4, 0, 0, -2, 0, 0, 0, 6, -2, 0, 0, -2, 0, 0, 0, 8, -4, 0,
     0, -1, 0, 0, 0, -4, -6, 0, 0, -6, 0, 0, 0, -4, -2, 0, 0, -6, 0, 0] := by
  eta_coeff

end WeightTwoCusps
