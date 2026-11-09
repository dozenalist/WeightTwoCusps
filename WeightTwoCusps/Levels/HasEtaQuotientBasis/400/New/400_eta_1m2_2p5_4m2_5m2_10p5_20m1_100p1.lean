module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^(-2) η(10z)^5 η(20z)^(-1) η(100z)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^(-2) η(10z)^5 η(20z)^(-1) η(100z)` at level 400. -/
abbrev cuspForm_400_eta_1m2_2p5_4m2_5m2_10p5_20m1_100p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -2, 1 => 5, 3 => -2, 4 => -2, 9 => 5, 19 => -1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m2_2p5_4m2_5m2_10p5_20m1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m2_2p5_4m2_5m2_10p5_20m1_100p1 =
    [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 2, 4, 0, 0, 6, 0, 0, 0, 0, 4,
     0, 2, 0, 0, 0, 1, 6, 0, 0, 2, 0, -4, 0, 0, -2, 4, 0, 0, 0, -4,
     0, 4, 0, 0, 0, -3, -6, 0, 0, -6, 2, 0, 0, 0, -4, -4, 0, 0, 0, 4,
     0, -4, 0, 0, 0, -2, -8, 0, 0, -2, -8, -4, 0, 0, -2, 0, 0, 0, 0, -8,
     0, -10, 0, 0, 0, 2, 2, 0, 0, 6, -6, 0, 0, 0, -10, -4, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
