module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 140

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-1) η(14z)^2 η(28z)^(-1) η(70z)`; see
[the local level table](../../TABLE.md#level-140).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-1) η(14z)^2 η(28z)^(-1) η(70z)` at level 140. -/
abbrev cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1 : gamma0CuspForms 140 :=
  etaQuotientCuspForm 140 sparse![140; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 13 => 2, 27 => -1, 69 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1_first_coeffs :
    first_coeffs 100 cuspForm_140_eta_1m2_2p4_4m1_5p2_10m1_14p2_28m1_70p1 =
    [0, 0, 0, 1, 2, 1, 2, 3, 0, 0, 2, 0, 0, 3, 0, 0, 2, -3, -4, -2,
     -4, -6, 0, -2, -4, 2, -2, -5, 0, 0, -6, 2, 0, -1, 2, -4, -2, 2, 0, -4,
     4, -2, 0, 0, 0, 0, 0, 1, -4, 8, 2, 4, 0, -2, -2, 1, -2, -4, 8, 2,
     6, 4, 4, 2, 2, 0, 2, 6, 4, 4, 4, 8, 4, -2, -8, -3, 0, 1, 4, -4,
     0, 0, -4, 0, 0, -2, -8, 3, 8, 4, 4, 6, -4, -2, 10, -2, 0, 5, 0, 4] := by
  eta_coeff

end WeightTwoCusps
