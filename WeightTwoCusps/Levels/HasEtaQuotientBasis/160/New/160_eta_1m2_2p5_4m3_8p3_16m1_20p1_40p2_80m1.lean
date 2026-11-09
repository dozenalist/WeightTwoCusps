module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 160

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^2 η(80z)^(-1)`; see
[the local level table](../../TABLE.md#level-160).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^2 η(80z)^(-1)` at level 160. -/
abbrev cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1 : gamma0CuspForms 160 :=
  etaQuotientCuspForm 160 sparse![160; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 19 => 1, 39 => 2, 79 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1 =
    [0, 1, 2, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, -2, 2, 0, 0, 2, -2, 0,
     0, 0, -4, 0, 0, -7, 0, 0, 0, -2, -2, 0, 0, 0, -4, 0, 0, -2, 0, 0,
     0, -2, -4, 0, 0, -9, -10, 0, 0, -3, 2, 0, 0, 6, -4, 0, 0, -8, 4, 0,
     0, -2, 12, 0, 0, 22, 0, 0, 0, 8, 6, 0, 0, 2, 8, 0, 0, 8, 4, 0,
     0, -3, 0, 0, 0, 6, 18, 0, 0, 2, -4, 0, 0, 0, 2, 0, 0, 10, 6, 0] := by
  eta_coeff

end WeightTwoCusps
