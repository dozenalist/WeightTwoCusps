module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z) η(4z) η(5z) η(10z) η(100z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z) η(5z) η(10z) η(100z)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p1_4p1_5p1_10p1_100p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 1, 3 => 1, 4 => 1, 9 => 1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p1_4p1_5p1_10p1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p1_4p1_5p1_10p1_100p1 =
    [0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 0, 2, 0, 2,
     2, 1, 0, 3, 0, 0, 3, -1, 0, 1, 0, -2, 2, 1, -1, 1, 0, -1, 0, -2,
     0, 2, 0, -3, 0, -1, -3, 3, -2, -3, 1, 0, -4, -1, -2, -2, 0, -3, 0, 2,
     -4, -2, 0, -1, 0, 0, -4, -4, 2, -1, -4, -2, -4, -4, -1, -1, 0, 2, 0, -4,
     0, -5, 0, -2, 0, -2, 1, -2, -6, 3, -3, 0, 0, -2, -5, 0, 0, -1, 0, -2] := by
  eta_coeff

end WeightTwoCusps
